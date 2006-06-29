/* SHA-1 cryptographic hash function */
/* Ref: Handbook of Applied Cryptography, section 9.4.2, algorithm 9.53 */

#include <string.h>

extern void memcpy_static(void *, void *, int),
  memset_static(void *, int, char);

#define memcpy memcpy_static
#define memset memset_static

#define ARCH_BIG_ENDIAN

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

static void SHA1_copy_and_swap(void * src, void * dst, int numwords)
{
#ifdef ARCH_BIG_ENDIAN
  memcpy(dst, src, numwords * sizeof(u32));
#else
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
#endif
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
