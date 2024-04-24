/* ecc-elgamal.c  -  Elliptic Curve ElGamal implementation
 * Copyright (C) 2024 Shouran MA
 *
 * This file is part of Libgcrypt.
 *
 * Libgcrypt is free software; you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as
 * published by the Free Software Foundation; either version 2.1 of
 * the License, or (at your option) any later version.
 *
 * Libgcrypt is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this program; if not, see <http://www.gnu.org/licenses/>.
 */

#include <config.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>

#include "g10lib.h"
#include "bithelp.h"
#include "mpi.h"
#include "cipher.h"
#include "context.h"
#include "ec-context.h"
#include "pubkey-internal.h"
#include "ecc-common.h"

#define MPI_NBYTES(m)   ((mpi_get_nbits(m) + 7) / 8)


/* Key derivation function from X9.63/SECG */
static gpg_err_code_t
kdf_x9_63 (int algo, const void *in, size_t inlen, void *out, size_t outlen)
{
  gpg_err_code_t rc;
  gcry_md_hd_t hd;
  int mdlen;
  u32 counter = 1;
  u32 counter_be;
  unsigned char *dgst;
  unsigned char *pout = out;
  size_t rlen = outlen;
  size_t len;

  rc = _gcry_md_open (&hd, algo, 0);
  if (rc)
    return rc;

  mdlen = _gcry_md_get_algo_dlen (algo);

  while (rlen > 0)
    {
      counter_be = be_bswap32 (counter);   /* cpu_to_be32 */
      counter++;

      _gcry_md_write (hd, in, inlen);
      _gcry_md_write (hd, &counter_be, sizeof(counter_be));

      dgst = _gcry_md_read (hd, algo);
      if (dgst == NULL)
        {
          rc = GPG_ERR_DIGEST_ALGO;
          break;
        }

      len = mdlen < rlen ? mdlen : rlen;  /* min(mdlen, rlen) */
      memcpy (pout, dgst, len);
      rlen -= len;
      pout += len;

      _gcry_md_reset (hd);
    }

  _gcry_md_close (hd);
  return rc;
}


/* _gcry_ecc_elgamal_encrypt description:
 *   input:
 *     data[0] : octet string
 *   output: A new S-expression with the parameters:
 *     a: c1 : generated ephemeral public key (kG)
 *     b: c3 : Hash(x2 || IN || y2)
 *     c: c2 : cipher
 *
 * elgamal_decrypt description:
 *   in contrast to encrypt
 */
gpg_err_code_t
_gcry_ecc_elgamal_encrypt (gcry_sexp_t *r_ciph, gcry_mpi_t input, mpi_ec_t ec)
{
  gpg_err_code_t rc;
  const int algo = GCRY_MD_SM3;
  gcry_md_hd_t md = NULL;
  int mdlen;
  unsigned char *dgst;
  gcry_mpi_t k = NULL;
  mpi_point_struct kG, kP;
  gcry_mpi_t x1, y1;
  gcry_mpi_t x2, y2;
  gcry_mpi_t x2y2 = NULL;
  unsigned char *in = NULL;
  unsigned int inlen;
  unsigned char *raw;
  unsigned int rawlen;
  unsigned char *cipher = NULL;
  int i;

  point_init (&kG);
  point_init (&kP);
  x1 = mpi_new (0);
  y1 = mpi_new (0);
  x2 = mpi_new (0);
  y2 = mpi_new (0);

  in = _gcry_mpi_get_buffer (input, 0, &inlen, NULL);
  if (!in)
    {
      rc = gpg_err_code_from_syserror ();
      if (DBG_CIPHER)
        log_debug ("ecc_encrypt    => %s\n", gpg_strerror (rc));
      goto leave;
    }

  cipher = xtrymalloc (inlen);
  if (!cipher)
    {
      rc = gpg_err_code_from_syserror ();
      goto leave;
    }

  /* rand k in [1, n-1] */
  k = _gcry_dsa_gen_k (ec->n, GCRY_VERY_STRONG_RANDOM);

  /* [k]G = (x1, y1) */
  _gcry_mpi_ec_mul_point (&kG, k, ec->G, ec);
  if (_gcry_mpi_ec_get_affine (x1, y1, &kG, ec))
    {
      if (DBG_CIPHER)
        log_debug ("Bad check: kG can not be a Point at Infinity!\n");
      rc = GPG_ERR_INV_DATA;
      goto leave;
    }

  /* [k]P = (x2, y2) */
  _gcry_mpi_ec_mul_point (&kP, k, ec->Q, ec);
  if (_gcry_mpi_ec_get_affine (x2, y2, &kP, ec))
    {
      rc = GPG_ERR_INV_DATA;
      goto leave;
    }

  /* t = KDF(x2 || y2, klen) */
  x2y2 = _gcry_mpi_ec_ec2os (&kP, ec);
  raw = mpi_get_opaque (x2y2, &rawlen);
  rawlen = (rawlen + 7) / 8;

  /* skip the prefix '0x04' */
  raw += 1;
  rawlen -= 1;
  rc = kdf_x9_63 (algo, raw, rawlen, cipher, inlen);
  if (rc)
    goto leave;

  /* cipher = t xor in */
  for (i = 0; i < inlen; i++)
    cipher[i] ^= in[i];

  /* hash(x2 || IN || y2) */
  mdlen = _gcry_md_get_algo_dlen (algo);
  rc = _gcry_md_open (&md, algo, 0);
  if (rc)
    goto leave;
  _gcry_md_write (md, raw, MPI_NBYTES(x2));
  _gcry_md_write (md, in, inlen);
  _gcry_md_write (md, raw + MPI_NBYTES(x2), MPI_NBYTES(y2));
  dgst = _gcry_md_read (md, algo);
  if (dgst == NULL)
    {
      rc = GPG_ERR_DIGEST_ALGO;
      goto leave;
    }

  if (!rc)
    {
      gcry_mpi_t c1;
      gcry_mpi_t c3;
      gcry_mpi_t c2;

      c3 = mpi_new (0);
      c2 = mpi_new (0);

      c1 = _gcry_ecc_ec2os (x1, y1, ec->p);
      _gcry_mpi_set_opaque_copy (c3, dgst, mdlen * 8);
      _gcry_mpi_set_opaque_copy (c2, cipher, inlen * 8);

      rc = sexp_build (r_ciph, NULL,
                       "(enc-val(flags elgamal)(elgamal(a%M)(b%M)(c%M)))",
                       c1, c3, c2);

      mpi_free (c1);
      mpi_free (c3);
      mpi_free (c2);
    }

leave:
  _gcry_md_close (md);
  mpi_free (x2y2);
  mpi_free (k);

  point_free (&kG);
  point_free (&kP);
  mpi_free (x1);
  mpi_free (y1);
  mpi_free (x2);
  mpi_free (y2);

  xfree (cipher);
  xfree (in);

  return rc;
}


gpg_err_code_t
_gcry_ecc_elgamal_decrypt (gcry_sexp_t *r_plain, gcry_sexp_t data_list, mpi_ec_t ec)
{
  gpg_err_code_t rc;
  gcry_mpi_t data_c1 = NULL;
  gcry_mpi_t data_c3 = NULL;
  gcry_mpi_t data_c2 = NULL;

  /*
   * Extract the data.
   */
  rc = sexp_extract_param (data_list, NULL, "/a/b/c",
                           &data_c1, &data_c3, &data_c2, NULL);
  if (rc)
    goto leave;
  if (DBG_CIPHER)
    {
      log_printmpi ("ecc_decrypt  d_c1", data_c1);
      log_printmpi ("ecc_decrypt  d_c3", data_c3);
      log_printmpi ("ecc_decrypt  d_c2", data_c2);
    }

  {
    const int algo = GCRY_MD_SM3;
    gcry_md_hd_t md = NULL;
    int mdlen;
    unsigned char *dgst;
    mpi_point_struct c1;
    mpi_point_struct kP;
    gcry_mpi_t x2, y2;
    gcry_mpi_t x2y2 = NULL;
    unsigned char *in = NULL;
    unsigned int inlen;
    unsigned char *plain = NULL;
    unsigned char *raw;
    unsigned int rawlen;
    unsigned char *c3 = NULL;
    unsigned int c3_len;
    int i;

    point_init (&c1);
    point_init (&kP);
    x2 = mpi_new (0);
    y2 = mpi_new (0);

    in = mpi_get_opaque (data_c2, &inlen);
    inlen = (inlen + 7) / 8;
    plain = xtrymalloc (inlen);
    if (!plain)
      {
        rc = gpg_err_code_from_syserror ();
        goto leave_main;
      }

    rc = _gcry_ecc_sec_decodepoint (data_c1, ec, &c1);
    if (rc)
      goto leave_main;

    if (!_gcry_mpi_ec_curve_point (&c1, ec))
      {
        rc = GPG_ERR_INV_DATA;
        goto leave_main;
      }

    /* [d]C1 = (x2, y2), C1 = [k]G */
    _gcry_mpi_ec_mul_point (&kP, ec->d, &c1, ec);
    if (_gcry_mpi_ec_get_affine (x2, y2, &kP, ec))
      {
        rc = GPG_ERR_INV_DATA;
        goto leave_main;
      }

    /* t = KDF(x2 || y2, inlen) */
    x2y2 = _gcry_mpi_ec_ec2os (&kP, ec);
    raw = mpi_get_opaque (x2y2, &rawlen);
    rawlen = (rawlen + 7) / 8;
    /* skip the prefix '0x04' */
    raw += 1;
    rawlen -= 1;
    rc = kdf_x9_63 (algo, raw, rawlen, plain, inlen);
    if (rc)
      goto leave_main;

    /* plain = C2 xor t */
    for (i = 0; i < inlen; i++)
      plain[i] ^= in[i];

    /* Hash(x2 || IN || y2) == C3 */
    mdlen = _gcry_md_get_algo_dlen (algo);
    rc = _gcry_md_open (&md, algo, 0);
    if (rc)
      goto leave_main;
    _gcry_md_write (md, raw, MPI_NBYTES(x2));
    _gcry_md_write (md, plain, inlen);
    _gcry_md_write (md, raw + MPI_NBYTES(x2), MPI_NBYTES(y2));
    dgst = _gcry_md_read (md, algo);
    if (dgst == NULL)
      {
        memset (plain, 0, inlen);
        rc = GPG_ERR_DIGEST_ALGO;
        goto leave_main;
      }
    c3 = mpi_get_opaque (data_c3, &c3_len);
    c3_len = (c3_len + 7) / 8;
    if (c3_len != mdlen || memcmp (dgst, c3, c3_len) != 0)
      {
        memset (plain, 0, inlen);
        rc = GPG_ERR_INV_DATA;
        goto leave_main;
      }

    if (!rc)
      {
        gcry_mpi_t r;

        r = mpi_new (inlen * 8);
        _gcry_mpi_set_buffer (r, plain, inlen, 0);

        rc = sexp_build (r_plain, NULL, "(value %m)", r);

        mpi_free (r);
      }

  leave_main:
    _gcry_md_close (md);
    mpi_free (x2y2);
    xfree (plain);

    point_free (&c1);
    point_free (&kP);
    mpi_free (x2);
    mpi_free (y2);
  }

 leave:
  _gcry_mpi_release (data_c1);
  _gcry_mpi_release (data_c3);
  _gcry_mpi_release (data_c2);

  return rc;
}
