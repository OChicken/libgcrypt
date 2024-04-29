/* ecelg.c - Test elliptic curve variant of ElGamal
 * Copyright (C) shouran.ma@eit.lth.se
 *
 * This file is free software; you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as
 * published by the Free Software Foundation; either version 2.1 of
 * the License, or (at your option) any later version.
 *
 * This file is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this program; if not, see <http://www.gnu.org/licenses/>.
 */

#ifdef HAVE_CONFIG_H
#include <config.h>
#endif

#define PGM "t-ecelg"
#include "t-common.h"
#include <string.h>
#include <fcntl.h>   /* open */
#include <unistd.h>  /* read, write, close */
#define SYMBYTES 32

static void
show_note (const char *format, ...)
{
  va_list arg_ptr;

  if (!verbose && getenv ("srcdir"))
    fputs ("      ", stderr);  /* To align above "PASS: ".  */
  else
    fprintf (stderr, "%s: ", PGM);
  va_start (arg_ptr, format);
  vfprintf (stderr, format, arg_ptr);
  if (*format && format[strlen(format)-1] != '\n')
    putc ('\n', stderr);
  va_end (arg_ptr);
}

static void
show_mpi (const char *text, gcry_mpi_t a)
{
  gcry_error_t err;
  char *buf;
  void *bufaddr = &buf;

  fprintf (stderr, "%s: ", PGM);
  err = gcry_mpi_aprint (GCRYMPI_FMT_HEX, bufaddr, NULL, a);
  if (err)
    fprintf (stderr, "%s: [error printing number: %s]\n",
             text, gpg_strerror (err));
  else
    {
      fprintf (stderr, "%s #%s#\n", text, buf);
      gcry_free (buf);
    }
}

static void
show_sexp (const char *prefix, gcry_sexp_t a)
{
  char *buf;
  size_t size;

  fprintf (stderr, "%s: ", PGM);
  if (prefix)
    fputs (prefix, stderr);
  size = gcry_sexp_sprint (a, GCRYSEXP_FMT_ADVANCED, NULL, 0);
  buf = xmalloc (size);

  gcry_sexp_sprint (a, GCRYSEXP_FMT_ADVANCED, buf, size);
  fprintf (stderr, "%.*s", (int)size, buf);
  gcry_free (buf);
}

static void*
hex2buffer (const char *string, size_t *r_length)
{
  const char *s;
  unsigned char *buffer;
  size_t length;

  buffer = xmalloc (strlen(string)/2+1);
  length = 0;
  for (s=string; *s; s +=2 )
    {
      if (!hexdigitp (s) || !hexdigitp (s+1))
        return NULL;           /* Invalid hex digits. */
      buffer[length++] = xtoi_2 (s);
    }
  *r_length = length;
  return buffer;
}

static void
show_hex (const char *prefix, const void *buf, size_t buflen)
{
  const unsigned char *s;
  fprintf (stderr, "%s: %s ", PGM, prefix);
  for (s= buf; buflen; buflen--, s++)
    fprintf (stderr, "%02x", *s);
  putc ('\n', stderr);
}

static gpg_error_t
check(gcry_mpi_t m)
{
  gpg_error_t err;
  unsigned char buf[SYMBYTES];
  int fd;
  char msg[SYMBYTES];

  /* write decrypted msg to buf */
  gcry_mpi_print(GCRYMPI_FMT_STD, buf, SYMBYTES, NULL, m);
  if (debug)
    show_note("decrypted msg: %s", buf);

  /* read answer from file */
  fd = open("nistp256.txt", O_RDONLY, 0644);
  read(fd, msg, SYMBYTES);
  close(fd);

  /* compare */
  err = strcmp((char *)buf, msg);
  if (err)
    fail("fail in dec when comparing with the original msg\n");
  else
    if (debug)
      show_note("Decrypted msg is consistent with the original msg.\n");

  return err;
}

static gpg_error_t
gcry_ecelg_check_encodable(gcry_mpi_t x, gcry_ctx_t ctx)
{
  gpg_error_t err = 0;
  gcry_mpi_t p, a, b;
  gcry_mpi_t rhs, tmp;

  /* alloc */
  p = gcry_mpi_ec_get_mpi("p", ctx, 1);
  a = gcry_mpi_ec_get_mpi("a", ctx, 1);
  b = gcry_mpi_ec_get_mpi("b", ctx, 1);
  rhs = gcry_mpi_new(0);
  tmp = gcry_mpi_new(0);

  /* rhs = x^3+ax+b */
  if (debug)
    show_note("Calculate rhs = x^3+ax+b, where x is the msg.\n");
  gcry_mpi_powm(rhs, x, GCRYMPI_CONST_THREE, p);  /* x^3      */
  gcry_mpi_mulm(tmp, a, x, p);                    /* ax       */
  gcry_mpi_addm(rhs, rhs, tmp, p);                /* x^3+ax   */
  gcry_mpi_addm(rhs, rhs, b, p);                  /* x^3+ax+b */

  /* Legendre symbol */
  if (debug)
    show_note("Calculate Legendre symbol Jp(rhs) = rhs^((p-1)/2) mod p\n");
  gcry_mpi_sub_ui(tmp, p, 1);
  gcry_mpi_div(tmp, NULL, tmp, GCRYMPI_CONST_TWO, 0);  /* (p-1)/2 */
  gcry_mpi_powm(tmp, rhs, tmp, p);
  if (!gcry_mpi_cmp_ui(tmp, 1))
    {
      if (debug)
        show_note("Jp(x^3+ax+b) = 1 ⇒ msg can be encoded to the curve.\n");
    }
  else
    {
      err = 1;
      fail("Jp(x^3+ax+b) ≠ 1 ⇒ msg CANNOT be encoded to the curve. "
           "It is required to be 1 to guarantee that the rhs of the EC equation"
           " is a square of the y coordinate so that the message is able to be "
           "encoded to the curve. But the msg fails to satisfy this criteria.\n");
    }

  /* release */
  gcry_mpi_release(p);
  gcry_mpi_release(a);
  gcry_mpi_release(b);
  gcry_mpi_release(rhs);
  gcry_mpi_release(tmp);
  return err;
}

static gpg_error_t
gcry_mpi_ec_get_y(gcry_mpi_t *y, gcry_mpi_t x, gcry_ctx_t ctx)
{
  gpg_error_t err = 0;
  gcry_mpi_t p, a, b;
  gcry_mpi_t rhs, tmp;

  /* alloc */
  p = gcry_mpi_ec_get_mpi("p", ctx, 1);
  a = gcry_mpi_ec_get_mpi("a", ctx, 1);
  b = gcry_mpi_ec_get_mpi("b", ctx, 1);
  rhs = gcry_mpi_new(0);
  tmp = gcry_mpi_new(0);

  /* rhs = x^3+ax+b */
  if (debug)
    show_note("Calculate rhs = x^3+ax+b, where x is the msg.\n");
  gcry_mpi_powm(rhs, x, GCRYMPI_CONST_THREE, p);  /* x^3      */
  gcry_mpi_mulm(tmp, a, x, p);                    /* ax       */
  gcry_mpi_addm(rhs, rhs, tmp, p);                /* x^3+ax   */
  gcry_mpi_addm(rhs, rhs, b, p);                  /* x^3+ax+b */

  /* calc y coordinate */
  if (debug)
    show_note("Calculate y = sqrt(rhs) mod p = rhs^((p+1)/4) mod p\n");
  gcry_mpi_add_ui(tmp, p, 1);
  gcry_mpi_div(tmp, NULL, tmp, GCRYMPI_CONST_FOUR, 0);  /* (p+1)/4 */
  gcry_mpi_powm(*y, rhs, tmp, p);

  /* release */
  gcry_mpi_release(p);
  gcry_mpi_release(a);
  gcry_mpi_release(b);
  gcry_mpi_release(rhs);
  gcry_mpi_release(tmp);
  return err;
}

static gpg_error_t
check_curve_Fp(gcry_ctx_t *ctx)
{
  gpg_error_t err = 0;
  gcry_mpi_t p;
  gcry_mpi_t r;  /* temporary result */

  /* print_banner("check curve's Fp: p%4=3 or not"); */

  /* alloc */
  p = gcry_mpi_ec_get_mpi("p", *ctx, 1);
  r = gcry_mpi_new(0);

  /* check p%4 == 3 */
  gcry_mpi_mod(r, p, GCRYMPI_CONST_FOUR);
  if (gcry_mpi_cmp_ui(r, 3))
  {
    fprintf(stderr, "Improper in choosing the curve param: p≭3 mod 4, "
	            "please choose another curve.\n");
    err = 1;
  }

  /* release */
  gcry_mpi_release(p);
  gcry_mpi_release(r);
  return err;
}

static void
ec_cast_to_affine(gcry_mpi_point_t *p, gcry_ctx_t ctx)
{
  gcry_mpi_t x, y, z;
  x = gcry_mpi_new(0);
  y = gcry_mpi_new(0);
  z = gcry_mpi_set_ui(NULL, 1);
  if (gcry_mpi_ec_get_affine(x, y, *p, ctx))
    fail ("failed to get affine coordinates\n");
  gcry_mpi_point_snatch_set(*p, x, y, z);
}

static void
check_ec_point_relation (gcry_sexp_t key)
{
  gcry_ctx_t ctx;
  gcry_mpi_point_t g, q, dg;
  gcry_mpi_t d;
  gcry_mpi_t gx, gy, gz;
  gcry_mpi_t qx, qy, qz;
  gcry_mpi_t dgx, dgy, dgz;

  /* alloc */
  gcry_mpi_ec_new (&ctx, key, NULL);
  gx  = gcry_mpi_new(0);
  gy  = gcry_mpi_new(0);
  gz  = gcry_mpi_new(0);
  qx  = gcry_mpi_new(0);
  qy  = gcry_mpi_new(0);
  qz  = gcry_mpi_new(0);
  dgx = gcry_mpi_new(0);
  dgy = gcry_mpi_new(0);
  dgz = gcry_mpi_new(0);
  dg  = gcry_mpi_point_new(0);

  /* get points g & q, and scalar d */
  g = gcry_mpi_ec_get_point("g", ctx, 1);
  q = gcry_mpi_ec_get_point("q", ctx, 1);
  d = gcry_mpi_ec_get_mpi  ("d", ctx, 1);

  /* get coordinate */
  gcry_mpi_point_get(gx, gy, gz, g);
  gcry_mpi_point_get(qx, qy, qz, q);

  /* check dg == q */
  gcry_mpi_ec_mul(dg, d, g, ctx);
  if (gcry_mpi_cmp_ui(dgz, 1))
    ec_cast_to_affine(&dg, ctx);
  gcry_mpi_point_get(dgx, dgy, dgz, dg);
  if (gcry_mpi_cmp(dgx, qx))
    fail ("dg != q in x coordinate!");
  if (gcry_mpi_cmp(dgy, qy))
    fail ("dg != q in y coordinate!");
  if (gcry_mpi_cmp(dgz, qz))
    fail ("dg != q in z coordinate!");

  if (debug)
    {
      show_mpi("d   ", d);
      show_mpi("g.X ", gx);
      show_mpi("g.Y ", gy);
      show_mpi("g.Z ", gz);
      show_mpi("q.X ", qx);
      show_mpi("q.Y ", qy);
      show_mpi("q.Z ", qz);
      show_mpi("dg.X", dgx);
      show_mpi("dg.Y", dgy);
      show_mpi("dg.Z", dgz);
    }

  /* release */
  gcry_mpi_point_release(g);
  gcry_mpi_point_release(q);
  gcry_mpi_point_release(dg);
  gcry_mpi_release(d);
  gcry_mpi_release(gx);
  gcry_mpi_release(gy);
  gcry_mpi_release(gz);
  gcry_mpi_release(qx);
  gcry_mpi_release(qy);
  gcry_mpi_release(qz);
  gcry_mpi_release(dgx);
  gcry_mpi_release(dgy);
  gcry_mpi_release(dgz);
  gcry_ctx_release(ctx);
}

static void
ecelg_keypair(gcry_sexp_t *sk, gcry_sexp_t *pk, const char *curve)
{
  gpg_error_t err;
  gcry_sexp_t keyparm, keypair;

  /* generate keys */
  /* print_banner("generate key pairs"); */
  err = gcry_sexp_build (&keyparm, NULL,
                         "(genkey(ecc(curve %s)(flags param)))", curve);
  if (err)
        die ("error creating S-expression: %s\n", gpg_strerror (err));

  err = gcry_pk_genkey (&keypair, keyparm);
  if (err)
    die ("error generating ECC key with curve %s: %s\n",
	 curve, gpg_strerror (err));
  if (debug)
    show_sexp("", keypair);

  /* gcry_pk_testkey should works on the entire S-expression.  */
  err = gcry_pk_testkey(keypair);
  if (err)
    fail ("gcry_pk_testkey failed on key pair: %s\n", gpg_strerror (err));

  /* get pk & sk from keypair */
  *pk = gcry_sexp_find_token (keypair, "public-key", 0);
  if (!*pk)
    fail ("public part missing in return value\n");
  *sk = gcry_sexp_find_token (keypair, "private-key", 0);
  if (!*sk)
    fail ("private part missing in return value\n");
  check_ec_point_relation(*sk);

  gcry_sexp_release(keyparm);
  gcry_sexp_release(keypair);
}

static void
ecelg_enc(gcry_sexp_t *ct, gcry_sexp_t pt, gcry_sexp_t pk)
{
  gcry_error_t err;
  gcry_ctx_t ctx;
  gcry_mpi_point_t g, q, c1, c2;
  gcry_mpi_t n, k;
  gcry_mpi_point_t m;
  gcry_mpi_t mx, my, c1x, c1y, c2x, c2y;

  /* get context from pk */
  gcry_mpi_ec_new(&ctx, pk, NULL);

  /* encode message to point m */
  m = gcry_mpi_point_new(0);
  my = gcry_mpi_new(0);
  if (debug)
    show_sexp("pt", pt);
  err = gcry_sexp_extract_param(pt, "data", "'value'", &mx, NULL);
  if (debug)
    show_mpi("mx", mx);
  gcry_mpi_ec_get_y(&my, mx, ctx);
  gcry_mpi_point_set(m, mx, my, GCRYMPI_CONST_ONE);
  if (debug)
    {
      show_note("m on curve? %d\n", gcry_mpi_ec_curve_point(m, ctx));
      show_mpi("m.X", mx);
      show_mpi("m.Y", my);
    }

  /* generate random k={0,...,q-1} */
  k = gcry_mpi_new(0);
  err = gcry_sexp_extract_param(pk, "public-key!ecc", "n", &n, NULL);
  if (err)
    fail ("gcry_sexp_extract_param failed: %s", gpg_strerror (err));
  unsigned int nbits = gcry_mpi_get_nbits(n);
  gcry_mpi_randomize(k, nbits, GCRY_WEAK_RANDOM);

  /* get points g & q */
  g = gcry_mpi_ec_get_point("g", ctx, 1);
  q = gcry_mpi_ec_get_point("q", ctx, 1);

  /* multiply to get c1, c2 */
  c1 = gcry_mpi_point_new(0);
  c2 = gcry_mpi_point_new(0);
  gcry_mpi_ec_mul(c1, k, g, ctx);   /* c1 = k*g */
  ec_cast_to_affine(&c1, ctx);
  gcry_mpi_ec_mul(c2, k, q, ctx);   /* c2 = k*q */
  gcry_mpi_ec_add(c2, c2, m, ctx);  /* c2 = m + k*q */
  ec_cast_to_affine(&c2, ctx);

  /* check c1 & c2 */
  if (debug)
    {
      show_note("c1 on curve? %d\n", gcry_mpi_ec_curve_point(c1, ctx));
      show_note("c2 on curve? %d\n", gcry_mpi_ec_curve_point(c2, ctx));
    }

  /* build c1 & c2 sexp */
  c1x = gcry_mpi_new(0);
  c1y = gcry_mpi_new(0);
  c2x = gcry_mpi_new(0);
  c2y = gcry_mpi_new(0);
  gcry_mpi_point_get(c1x, c1y, NULL, c1);
  gcry_mpi_point_get(c2x, c2y, NULL, c2);
  err = gcry_sexp_build(ct, NULL,
			"(enc-val(ecelg(c1_x%m)(c1_y%m)(c2_x%m)(c2_y%m)))",
			c1x, c1y, c2x, c2y);
  if (debug)
    show_sexp("ct", *ct);

  /* release */
  gcry_mpi_point_release(g);
  gcry_mpi_point_release(q);
  gcry_mpi_point_release(c1);
  gcry_mpi_point_release(c2);
  gcry_mpi_release(n);
  gcry_mpi_release(k);
  gcry_mpi_point_release(m);
  gcry_mpi_release(mx);
  gcry_mpi_release(my);
  gcry_mpi_release(c1x);
  gcry_mpi_release(c1y);
  gcry_mpi_release(c2x);
  gcry_mpi_release(c2y);
  gcry_ctx_release(ctx);
}

static gpg_error_t
ecelg_dec(gcry_sexp_t ct, gcry_sexp_t sk)
{
  gpg_error_t err;
  gcry_ctx_t ctx;
  gcry_mpi_t p, d;
  gcry_mpi_point_t c1, c2, m;
  gcry_mpi_t mx, c1x, c1y, c2x, c2y;

  /* get context from sk */
  gcry_mpi_ec_new(&ctx, sk, NULL);

  /* get points c1 & c2 */
  c1 = gcry_mpi_point_new(0);
  c2 = gcry_mpi_point_new(0);
  err = gcry_sexp_extract_param(ct, "enc-val!ecelg",
				"'c1_x' 'c1_y' 'c2_x' 'c2_y'",
				&c1x, &c1y, &c2x, &c2y, NULL);
  if (err)
    fail ("gcry_sexp_extract_param failed: %s", gpg_strerror (err));
  gcry_mpi_point_set(c1, c1x, c1y, GCRYMPI_CONST_ONE);
  gcry_mpi_point_set(c2, c2x, c2y, GCRYMPI_CONST_ONE);

  /* get module p and private key d */
  err = gcry_sexp_extract_param(sk, "private-key!ecc", "p d", &p, &d, NULL);

  /* c1 ← d*c1 */
  if (debug)
    show_note("c1 ← d*c1\n");
  gcry_mpi_ec_mul(c1, d, c1, ctx);
  ec_cast_to_affine(&c1, ctx);
  if (debug)
    show_note("d*c1 on curve? %d\n", gcry_mpi_ec_curve_point(c1, ctx));

  /* m = c2 - d*c1 */
  if (debug)
    show_note("m = c2 - d*c1");
  m = gcry_mpi_point_new(0);
  gcry_mpi_ec_sub(m, c2, c1, ctx);
  ec_cast_to_affine(&m, ctx);
  if (debug)
    show_note("c2-d*c1 on curve? %d\n", gcry_mpi_ec_curve_point(m, ctx));

  /* check msg */
  mx = gcry_mpi_new(0);
  gcry_mpi_point_get(mx, NULL, NULL, m);
  if (debug)
    show_mpi("mx", mx);
  err = check(mx);

  /* release */
  gcry_mpi_point_release(m);
  gcry_mpi_point_release(c1);
  gcry_mpi_point_release(c2);
  gcry_mpi_release(d);
  gcry_mpi_release(p);
  gcry_mpi_release(mx);
  gcry_mpi_release(c1x);
  gcry_mpi_release(c1y);
  gcry_mpi_release(c2x);
  gcry_mpi_release(c2y);
  gcry_ctx_release(ctx);
  return err;
}

static gpg_error_t
ecelg_set_data(gcry_sexp_t *pt, const char *curve,
	       const char *flags, const char *hexstr)
{
  gpg_error_t err;
  gcry_mpi_t mx;
  size_t nscanned;
  char rd[SYMBYTES];
  void *wr;
  size_t buflen;
  char filename[12];
  size_t size;
  int fd;
  gcry_ctx_t ctx;

  sprintf(filename, "%s.txt", curve);

  /* convert hex string to buf string, len(hex) = 2*len(buf) */
  wr = hex2buffer(hexstr, &buflen);

  /* write buffer to file */
  fd = open(filename, O_WRONLY | O_CREAT, 0644);
  size = write(fd, wr, buflen);
  close(fd);
  if (debug)
    show_note("strlen=%lu, size=%lu, buflen=%lu, %s", strlen(wr), size, buflen, wr);

  /* read from file to buffer */
  fd = open(filename, O_RDONLY, 0);
  buflen = read(fd, rd, size);
  close(fd);
  if (debug)
    show_note("strlen=%lu, size=%lu, buflen=%lu, %s", strlen(wr), size, buflen, rd);

  /* scan to mpi */
  err = gcry_mpi_scan(&mx, GCRYMPI_FMT_STD, rd, buflen, &nscanned);
  if (err)
    fail ("error scanning content: %s\n", gpg_strerror (err));

  /* init ec ctx */
  gcry_mpi_ec_new(&ctx, NULL, curve);

  /* check curve Fp */
  err = check_curve_Fp(&ctx);
  if (err)
    fail("p != 3 (mod 4)\n");

  /* check encodable */
  err = gcry_ecelg_check_encodable(mx, ctx);
  if (err)
    goto release;

  /* build sexp with mpi */
  err = gcry_sexp_build (pt, NULL, "(data (flags %s) (value %m))", flags, mx);
  if (err)
    fail ("error building SEXP: %s", gpg_strerror (err));

  if (debug)
    {
      show_hex("read bell.txt", rd, buflen);
      show_sexp("pt", *pt);
    }

release:
  gcry_mpi_release(mx);
  gcry_ctx_release(ctx);
  free(wr);
  return err;
}

void
user_space(const char *msg)
{
  gpg_error_t err;
  gcry_sexp_t sk, pk;
  gcry_sexp_t pt, ct;

  /* alloc */
  gcry_sexp_new(&sk, NULL, 0, 1);
  gcry_sexp_new(&pk, NULL, 0, 1);
  gcry_sexp_new(&ct, NULL, 0, 1);
  gcry_sexp_new(&pt, NULL, 0, 1);

  const char curve[] = "nistp256";

  err = ecelg_set_data(&pt, curve, "raw", msg);
  if (err)
    goto release;
  ecelg_keypair(&sk, &pk, curve);
  ecelg_enc(&ct, pt, pk);
  err = ecelg_dec(ct, sk);
  if (err)
    fail("fail in decryption\n");

  if (debug)
    show_note("Result: %s\n", gpg_strerror(err));

release:
  gcry_sexp_release(sk);
  gcry_sexp_release(pk);
  gcry_sexp_release(pt);
  gcry_sexp_release(ct);
}

void
rebuild_lib(const char *msg)
{
  gpg_error_t err;
  gcry_sexp_t sk, pk;
  gcry_sexp_t keyparm;
  gcry_sexp_t keypair;
  gcry_sexp_t pt, ct;
  gcry_mpi_t m;

  ecelg_set_data(&pt, "elgamal", "elgamal", msg);
  if (debug)
    show_sexp("pt: ", pt);
  err = gcry_sexp_build(&keyparm, NULL, "(genkey(ecc(curve elgamal)))");
  err = gcry_pk_genkey(&keypair, keyparm);
  pk = gcry_sexp_find_token(keypair, "public-key", 0);
  sk = gcry_sexp_find_token(keypair, "private-key", 0);
  if (debug)
    {
      show_sexp("pk ", pk);
      show_sexp("sk ", sk);
    }

  err = gcry_pk_encrypt (&ct, pt, pk);
  if (debug)
    show_sexp("ct: ", ct);
  gcry_sexp_release (pt);

  /* decryption */
  err = gcry_pk_decrypt (&pt, ct, sk);
  if (debug)
    show_sexp("pt: ", pt);
  gcry_sexp_release (ct);

  /* check */
  err = gcry_sexp_extract_param(pt, "value", "'value'", &m, NULL);
  err = check(m);
  gcry_sexp_release (pt);
  gcry_mpi_release(m);

  /* release */
  gcry_sexp_release (pk);
  gcry_sexp_release (sk);
  gcry_sexp_release(keyparm);
  gcry_sexp_release(keypair);

  if (debug)
    show_note("Result: %s\n", gpg_strerror(err));
}

int
main (int argc, char **argv)
{
  int last_argc = -1;


  if (argc)
    { argc--; argv++; }

  while (argc && last_argc != argc )
    {
      last_argc = argc;
      if (!strcmp (*argv, "--"))
        {
          argc--; argv++;
          break;
        }
      else if (!strcmp (*argv, "--help"))
        {
          fputs ("usage: " PGM " [options]\n"
                 "Options:\n"
                 "  --verbose       print timings etc.\n"
                 "  --debug         flyswatter\n",
                 stdout);
          exit (0);
        }
      else if (!strcmp (*argv, "--verbose"))
        {
          verbose++;
          argc--; argv++;
        }
      else if (!strcmp (*argv, "--debug"))
        {
          verbose += 2;
          debug++;
          argc--; argv++;
        }
      else if (!strncmp (*argv, "--", 2))
        die ("unknown option '%s'", *argv);
    }

  xgcry_control ((GCRYCTL_DISABLE_SECMEM, 0));
  if (!gcry_check_version (GCRYPT_VERSION))
    die ("version mismatch\n");
  if (debug)
    xgcry_control ((GCRYCTL_SET_DEBUG_FLAGS, 1u , 0));
  xgcry_control ((GCRYCTL_ENABLE_QUICK_RANDOM, 0));
  xgcry_control ((GCRYCTL_INITIALIZATION_FINISHED, 0));

  const char msg[] =
	 /* "112233445566778899AABBCCDDEEFF00123456789ABCDEF0123456789ABCDEF0" */
	  "73686f7572616e2e6d61406569742e6c74682e7365204f436869636b656e0a00";
         /* "4544494E303546406569742e6c74682e73652020202020202020202020070a00"; */

  user_space(msg);
  rebuild_lib(msg);

  return !!error_count;
}
