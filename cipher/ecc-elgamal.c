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
  int mdlen;
  unsigned char *dgst;
  gcry_mpi_t k = NULL;
  mpi_point_struct M, kG, kQ;
  gcry_mpi_t x, y;
  gcry_mpi_t c1, c2;

  point_init (&M);
  point_init (&kG);
  point_init (&kQ);
  y  = mpi_new (0);

  x = _gcry_ecc_ec_patch_x (input, ec->p);
  rc = _gcry_ecc_sec_decodepoint (x, ec, &M);
  log_debug("on curve? %d\n", _gcry_mpi_ec_curve_point(&M, ec));
  if (_gcry_mpi_ec_get_affine (x, y, &M, ec))
    {
      rc = GPG_ERR_INV_DATA;
      goto leave;
    }
  log_debug("on curve? %d\n", _gcry_mpi_ec_curve_point(&M, ec));
  log_printpnt ("ecc_encrypt    M", &M, NULL);

  /* rand k in [1, n-1] */
  k = _gcry_dsa_gen_k (ec->n, GCRY_VERY_STRONG_RANDOM);
  log_printmpi ("k = ", k);

  /* kG <- [k]G */
  _gcry_mpi_ec_mul_point (&kG, k, ec->G, ec);
  if (_gcry_mpi_ec_get_affine (x, y, &kG, ec))
    {
      if (DBG_CIPHER)
        log_debug ("Bad check: kG can not be a Point at Infinity!\n");
      rc = GPG_ERR_INV_DATA;
      goto leave;
    }
  if (!rc)
    c1 = _gcry_ecc_ec2os (x, y, ec->p);

  /* kQ <- M+[k]Q */
  _gcry_mpi_ec_mul_point (&kQ, k, ec->Q, ec);
  _gcry_mpi_ec_add_points (&kQ, &M, &kQ, ec);
  if (_gcry_mpi_ec_get_affine (x, y, &kQ, ec))
    {
      rc = GPG_ERR_INV_DATA;
      goto leave;
    }
  if (!rc)
    c2 = _gcry_ecc_ec2os (x, y, ec->p);

  if (!rc)
    rc = sexp_build (r_ciph, NULL,
                     "(enc-val(flags elgamal)(elgamal(a%m)(b%m)))", c1, c2);

leave:
  point_free (&M);
  point_free (&kG);
  point_free (&kQ);
  mpi_free (k);
  mpi_free (x);
  mpi_free (y);
  mpi_free (c1);
  mpi_free (c2);

  return rc;
}


gpg_err_code_t
_gcry_ecc_elgamal_decrypt (gcry_sexp_t *r_plain, gcry_sexp_t data_list, mpi_ec_t ec)
{
  gpg_err_code_t rc;
  gcry_mpi_t data_c1 = NULL;
  gcry_mpi_t data_c2 = NULL;

  /*
   * Extract the data.
   */
  rc = sexp_extract_param (data_list, NULL, "ab", &data_c1, &data_c2, NULL);
  if (rc)
    goto leave;
  if (DBG_CIPHER)
    {
      log_printmpi ("ecc_decrypt  d_c1", data_c1);
      log_printmpi ("ecc_decrypt  d_c2", data_c2);
    }

  {
    mpi_point_struct c1;
    mpi_point_struct c2;
    mpi_point_struct M;
    gcry_mpi_t x, y;

    point_init (&c1);
    point_init (&c2);
    point_init (&M);
    x = mpi_new (0);
    y = mpi_new (0);

    /* get and check c1 */
    rc = _gcry_ecc_sec_decodepoint (data_c1, ec, &c1);
    if (rc)
      goto leave_main;
    if (!_gcry_mpi_ec_curve_point (&c1, ec))
      {
        rc = GPG_ERR_INV_DATA;
        goto leave_main;
      }

    /* get and check c2 */
    rc = _gcry_ecc_sec_decodepoint(data_c2, ec, &c2);
    if (rc)
      goto leave_main;
    if (!_gcry_mpi_ec_curve_point(&c2, ec))
      {
	rc = GPG_ERR_INV_DATA;
	goto leave_main;
      }

    /* c1 <- [d]c1, where c1 = [k]G */
    _gcry_mpi_ec_mul_point (&c1, ec->d, &c1, ec);
    if (_gcry_mpi_ec_get_affine (x, y, &c1, ec))
      {
        rc = GPG_ERR_INV_DATA;
        goto leave_main;
      }

    /* M = c2 - d*c1 */
    _gcry_mpi_ec_sub_points (&M, &c2, &c1, ec);
    if (_gcry_mpi_ec_get_affine (x, NULL, &M, ec))
      {
        rc = GPG_ERR_INV_DATA;
        goto leave_main;
      }
    if (!rc)
      {
        rc = sexp_build (r_plain, NULL, "(value %m)", x);
      }

  leave_main:
    point_free (&M);
    point_free (&c1);
    point_free (&c2);
    mpi_free (x);
    mpi_free (y);
  }

 leave:
  _gcry_mpi_release (data_c1);
  _gcry_mpi_release (data_c2);

  return rc;
}
