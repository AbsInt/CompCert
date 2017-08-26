/* SHA-1 cryptographic hash function */
/* Ref: Handbook of Applied Cryptography, section 9.4.2, algorithm 9.53 */

#include <string.h>
#include <stdio.h>
#include <stdlib.h>

typedef unsigned int u32;

struct SHA1Context {
  u32 state[5];
  u32 length[2];
  int numbytes;
  unsigned char buffer[64];
};

#define rol1(x) (((x) << 1) | ((x) >> 31))
#define rol5(x) (((x) << 5) | ((x) >> 27))
#define rol30(x) (((x) << 30) | ((x) >> 2))

static int arch_big_endian;

static void SHA1_copy_and_swap(void * src, void * dst, int numwords)
{
  if (arch_big_endian) {
    memcpy(dst, src, numwords * sizeof(u32));
  } else {
    unsigned char * s, * d;
    unsigned char a, b;
    for (s = src, d = dst; numwords > 0; s += 4, d += 4, numwords--) {
      a = s[0];
      b = s[1];
      d[0] = s[3];
      d[1] = s[2];
      d[2] = b;
      d[3] = a;
    }
  }
}

#define F(x,y,z) ( z ^ (x & (y ^ z) ) )
#define G(x,y,z) ( (x & y) | (z & (x | y) ) )
#define H(x,y,z) ( x ^ y ^ z )

#define Y1 0x5A827999U
#define Y2 0x6ED9EBA1U
#define Y3 0x8F1BBCDCU
#define Y4 0xCA62C1D6U

static void SHA1_transform(struct SHA1Context * ctx)
{
  int i;
  register u32 a, b, c, d, e, t;
  u32 data[80];

  /* Convert buffer data to 16 big-endian integers */
  SHA1_copy_and_swap(ctx->buffer, data, 16);

  /* Expand into 80 integers */
  for (i = 16; i < 80; i++) {
    t = data[i-3] ^ data[i-8] ^ data[i-14] ^ data[i-16];
    data[i] = rol1(t);
  }

  /* Initialize working variables */
  a = ctx->state[0];
  b = ctx->state[1];
  c = ctx->state[2];
  d = ctx->state[3];
  e = ctx->state[4];

  /* Perform rounds */
  for (i = 0; i < 20; i++) {
    t = F(b, c, d) + Y1 + rol5(a) + e + data[i];
    e = d; d = c; c = rol30(b); b = a; a = t;
  }
  for (/*nothing*/; i < 40; i++) {
    t = H(b, c, d) + Y2 + rol5(a) + e + data[i];
    e = d; d = c; c = rol30(b); b = a; a = t;
  }
  for (/*nothing*/; i < 60; i++) {
    t = G(b, c, d) + Y3 + rol5(a) + e + data[i];
    e = d; d = c; c = rol30(b); b = a; a = t;
  }
  for (/*nothing*/; i < 80; i++) {
    t = H(b, c, d) + Y4 + rol5(a) + e + data[i];
    e = d; d = c; c = rol30(b); b = a; a = t;
  }

  /* Update chaining values */
  ctx->state[0] += a;
  ctx->state[1] += b;
  ctx->state[2] += c;
  ctx->state[3] += d;
  ctx->state[4] += e;
}

void SHA1_init(struct SHA1Context * ctx)
{
  ctx->state[0] = 0x67452301U;
  ctx->state[1] = 0xEFCDAB89U;
  ctx->state[2] = 0x98BADCFEU;
  ctx->state[3] = 0x10325476U;
  ctx->state[4] = 0xC3D2E1F0U;
  ctx->numbytes = 0;
  ctx->length[0] = 0;
  ctx->length[1] = 0;
}

void SHA1_add_data(struct SHA1Context * ctx, unsigned char * data,
                   unsigned long len)
{
  u32 t;

  /* Update length */
  t = ctx->length[1];
  if ((ctx->length[1] = t + (u32) (len << 3)) < t)
    ctx->length[0]++;    /* carry from low 32 bits to high 32 bits */
  ctx->length[0] += (u32) (len >> 29);

  /* If data was left in buffer, pad it with fresh data and munge block */
  if (ctx->numbytes != 0) {
    t = 64 - ctx->numbytes;
    if (len < t) {
      memcpy(ctx->buffer + ctx->numbytes, data, len);
      ctx->numbytes += len;
      return;
    }
    memcpy(ctx->buffer + ctx->numbytes, data, t);
    SHA1_transform(ctx);
    data += t;
    len -= t;
  }
  /* Munge data in 64-byte chunks */
  while (len >= 64) {
    memcpy(ctx->buffer, data, 64);
    SHA1_transform(ctx);
    data += 64;
    len -= 64;
  }
  /* Save remaining data */
  memcpy(ctx->buffer, data, len);
  ctx->numbytes = len;
}

void SHA1_finish(struct SHA1Context * ctx, unsigned char output[20])
{
  int i = ctx->numbytes;

  /* Set first char of padding to 0x80. There is always room. */
  ctx->buffer[i++] = 0x80;
  /* If we do not have room for the length (8 bytes), pad to 64 bytes
     with zeroes and munge the data block */
  if (i > 56) {
    memset(ctx->buffer + i, 0, 64 - i);
    SHA1_transform(ctx);
    i = 0;
  }
  /* Pad to byte 56 with zeroes */
  memset(ctx->buffer + i, 0, 56 - i);
  /* Add length in big-endian */
  SHA1_copy_and_swap(ctx->length, ctx->buffer + 56, 2);
  /* Munge the final block */
  SHA1_transform(ctx);
  /* Final hash value is in ctx->state modulo big-endian conversion */
  SHA1_copy_and_swap(ctx->state, output, 5);
}

/* Test harness */

static void do_test(unsigned char * txt, unsigned char * expected_output)
{
  struct SHA1Context ctx;
  unsigned char output[20];
  int ok;

  SHA1_init(&ctx);
  SHA1_add_data(&ctx, txt, strlen((char *) txt));
  SHA1_finish(&ctx, output);
  ok = memcmp(output, expected_output, 20) == 0;
  printf("Test `%s': %s\n",
         (char *) txt, (ok ? "passed" : "FAILED"));
}

/*  Test vectors:
 *
 *  "abc"
 *  A999 3E36 4706 816A BA3E  2571 7850 C26C 9CD0 D89D
 *
 *  "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
 *  8498 3E44 1C3B D26E BAAE  4AA1 F951 29E5 E546 70F1
 */

unsigned char test_input_1[] = "abc";

unsigned char test_output_1[20] =
{ 0xA9, 0x99, 0x3E, 0x36, 0x47, 0x06, 0x81, 0x6A, 0xBA, 0x3E ,
  0x25, 0x71, 0x78, 0x50, 0xC2, 0x6C, 0x9C, 0xD0, 0xD8, 0x9D };

unsigned char test_input_2[] =
  "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";

unsigned char test_output_2[20] =
{ 0x84, 0x98, 0x3E, 0x44, 0x1C, 0x3B, 0xD2, 0x6E, 0xBA, 0xAE,
  0x4A, 0xA1, 0xF9, 0x51, 0x29, 0xE5, 0xE5, 0x46, 0x70, 0xF1 };


static void do_bench(int nblocks)
{
  struct SHA1Context ctx;
  unsigned char output[20];
  unsigned char data[64];
  int i;

  for (i = 0; i < 64; i++) data[i] = i;
  SHA1_init(&ctx);
  for (; nblocks > 0; nblocks--)
    SHA1_add_data(&ctx, data, 64);
  SHA1_finish(&ctx, output);
}

int main(int argc, char ** argv)
{
  /* Determine endianness */
  union { int i; unsigned char b[4]; } u;
  u.i = 0x12345678;
  switch (u.b[0]) {
  case 0x12: arch_big_endian = 1; break;
  case 0x78: arch_big_endian = 0; break;
  default: printf("Cannot determine endianness\n"); return 2;
  }
  do_test(test_input_1, test_output_1);
  do_test(test_input_2, test_output_2);
  do_bench(200000);
  return 0;
}
