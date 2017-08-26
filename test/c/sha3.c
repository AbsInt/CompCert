/* SHA-3 (Keccak) cryptographic hash function */
/* Code adapted from the "readable" implementation written by
   Markku-Juhani O. Saarinen <mjos@iki.fi> */

#include <stdio.h>
#include <string.h>

typedef unsigned long long uint64;
typedef unsigned char uint8;

#define KECCAK_ROUNDS 24

#define ROTL64(x, y) (((x) << (y)) | ((x) >> (64 - (y))))

const uint64 keccakf_rndc[24] = 
{
    0x0000000000000001, 0x0000000000008082, 0x800000000000808a,
    0x8000000080008000, 0x000000000000808b, 0x0000000080000001,
    0x8000000080008081, 0x8000000000008009, 0x000000000000008a,
    0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
    0x000000008000808b, 0x800000000000008b, 0x8000000000008089,
    0x8000000000008003, 0x8000000000008002, 0x8000000000000080, 
    0x000000000000800a, 0x800000008000000a, 0x8000000080008081,
    0x8000000000008080, 0x0000000080000001, 0x8000000080008008
};

const int keccakf_rotc[24] = 
{
    1,  3,  6,  10, 15, 21, 28, 36, 45, 55, 2,  14, 
    27, 41, 56, 8,  25, 43, 62, 18, 39, 61, 20, 44
};

const int keccakf_piln[24] = 
{
    10, 7,  11, 17, 18, 3, 5,  16, 8,  21, 24, 4, 
    15, 23, 19, 13, 12, 2, 20, 14, 22, 9,  6,  1 
};

// update the state with KECCAK_ROUND rounds

void keccakf(uint64 st[25])
{
    int j, round;
    uint64 t, bc[5];

    for (round = 0; round < KECCAK_ROUNDS; round++) {

        // Theta
#define THETA1(i) \
            bc[i] = st[i] ^ st[i + 5] ^ st[i + 10] ^ st[i + 15] ^ st[i + 20]

      THETA1(0); THETA1(1); THETA1(2); THETA1(3); THETA1(4);

#define THETA2(i) \
            t = bc[(i + 4) % 5] ^ ROTL64(bc[(i + 1) % 5], 1); \
            st[0 + i] ^= t; \
            st[5 + i] ^= t; \
            st[10 + i] ^= t; \
            st[15 + i] ^= t; \
            st[20 + i] ^= t

      THETA2(0); THETA2(1); THETA2(2); THETA2(3); THETA2(4);


        // Rho Pi

#define RHOPI(i, rotc) \
            j = keccakf_piln[i]; \
            bc[0] = st[j]; \
            st[j] = ROTL64(t, rotc); \
            t = bc[0]

        t = st[1];
        RHOPI(0, 1); RHOPI(1, 3); RHOPI(2, 6); RHOPI(3, 10);
        RHOPI(4, 15); RHOPI(5, 21); RHOPI(6, 28); RHOPI(7, 36);
        RHOPI(8, 45); RHOPI(9, 55); RHOPI(10, 2); RHOPI(11, 14);
        RHOPI(12, 27); RHOPI(13, 41); RHOPI(14, 56); RHOPI(15, 8);
        RHOPI(16, 25); RHOPI(17, 43); RHOPI(18, 62); RHOPI(19, 18);
        RHOPI(20, 39); RHOPI(21, 61); RHOPI(22, 20); RHOPI(23, 44);

        //  Chi

#define CHI1(i,j) \
                bc[i] = st[j + i]
#define CHI2(i,j) \
                st[j + i] ^= (~bc[(i + 1) % 5]) & bc[(i + 2) % 5]

        for (j = 0; j < 25; j += 5) {
          CHI1(0,j); CHI1(1,j); CHI1(2,j); CHI1(3,j); CHI1(4,j);
          CHI2(0,j); CHI2(1,j); CHI2(2,j); CHI2(3,j); CHI2(4,j);
        }

        //  Iota
        st[0] ^= keccakf_rndc[round];
    }
}

// read a 64-bit integer in little endian at the given address

static inline uint64 get64le(const uint8 *p)
{
  unsigned int l = p[0] | (p[1] << 8) | (p[2] << 16) | (p[3] << 24);
  unsigned int h = p[4] | (p[5] << 8) | (p[6] << 16) | (p[7] << 24);
  return l | ((uint64) h << 32);
}

// write a 64-bit integer in little endian at the given address

static inline void set64le(uint8 * p, uint64 x)
{
  p[0] = x;       p[1] = x >> 8;  p[2] = x >> 16; p[3] = x >> 24;
  p[4] = x >> 32; p[5] = x >> 40; p[6] = x >> 48; p[7] = x >> 56;
}

// compute a keccak hash (md) of the given byte length from "in"

void keccak(const uint8 *in, int inlen, uint8 *md, int mdlen)
{
    uint64 st[25];    
    uint8 temp[144];
    int i, rsiz, rsizw;

    rsiz = 200 - 2 * mdlen;
    rsizw = rsiz / 8;
    
    memset(st, 0, sizeof(st));

    for ( ; inlen >= rsiz; inlen -= rsiz, in += rsiz) {
        for (i = 0; i < rsizw; i++)
          st[i] ^= get64le(in + i * 8);
        keccakf(st);
    }
    
    // last block and padding
    memcpy(temp, in, inlen);
    temp[inlen++] = 1;
    memset(temp + inlen, 0, rsiz - inlen);
    temp[rsiz - 1] |= 0x80;

    for (i = 0; i < rsizw; i++)
      st[i] ^= get64le(temp + i * 8);

    keccakf(st);

    for(i = 0; i < 8; i++)
      set64le(temp + i * 8, st[i]);

    memcpy (md, temp, mdlen);
}

// test vectors

typedef struct {
    int mdlen;
    char *msgstr;
    uint8 md[64];
} test_triplet_t;

test_triplet_t testvec[4] = {   
  {
    28, "Keccak-224 Test Hash", {
      0x30, 0x04, 0x5B, 0x34, 0x94, 0x6E, 0x1B, 0x2E, 
      0x09, 0x16, 0x13, 0x36, 0x2F, 0xD2, 0x2A, 0xA0, 
      0x8E, 0x2B, 0xEA, 0xFE, 0xC5, 0xE8, 0xDA, 0xEE, 
      0x42, 0xC2, 0xE6, 0x65 }
  }, {
    32, "Keccak-256 Test Hash", {
      0xA8, 0xD7, 0x1B, 0x07, 0xF4, 0xAF, 0x26, 0xA4, 
      0xFF, 0x21, 0x02, 0x7F, 0x62, 0xFF, 0x60, 0x26, 
      0x7F, 0xF9, 0x55, 0xC9, 0x63, 0xF0, 0x42, 0xC4, 
      0x6D, 0xA5, 0x2E, 0xE3, 0xCF, 0xAF, 0x3D, 0x3C }
  }, {
    48, "Keccak-384 Test Hash", {
      0xE2, 0x13, 0xFD, 0x74, 0xAF, 0x0C, 0x5F, 0xF9, 
      0x1B, 0x42, 0x3C, 0x8B, 0xCE, 0xEC, 0xD7, 0x01, 
      0xF8, 0xDD, 0x64, 0xEC, 0x18, 0xFD, 0x6F, 0x92, 
      0x60, 0xFC, 0x9E, 0xC1, 0xED, 0xBD, 0x22, 0x30, 
      0xA6, 0x90, 0x86, 0x65, 0xBC, 0xD9, 0xFB, 0xF4, 
      0x1A, 0x99, 0xA1, 0x8A, 0x7D, 0x9E, 0x44, 0x6E }
  }, {
    64, "Keccak-512 Test Hash", {
      0x96, 0xEE, 0x47, 0x18, 0xDC, 0xBA, 0x3C, 0x74, 
      0x61, 0x9B, 0xA1, 0xFA, 0x7F, 0x57, 0xDF, 0xE7, 
      0x76, 0x9D, 0x3F, 0x66, 0x98, 0xA8, 0xB3, 0x3F, 
      0xA1, 0x01, 0x83, 0x89, 0x70, 0xA1, 0x31, 0xE6, 
      0x21, 0xCC, 0xFD, 0x05, 0xFE, 0xFF, 0xBC, 0x11, 
      0x80, 0xF2, 0x63, 0xC2, 0x7F, 0x1A, 0xDA, 0xB4, 
      0x60, 0x95, 0xD6, 0xF1, 0x25, 0x33, 0x14, 0x72, 
      0x4B, 0x5C, 0xBF, 0x78, 0x28, 0x65, 0x8E, 0x6A }
  }
};

#define DATALEN 100000
#define NITER 25

int main()
{
  static uint8 data[DATALEN];
  int i;
  uint8 md[64];

  // test

  for (i = 0; i < 4; i++) {
    
    keccak((uint8 *) testvec[i].msgstr, 
           strlen(testvec[i].msgstr),
           md, testvec[i].mdlen);

    printf("SHA-3 %d %s\n",
           testvec[i].mdlen * 8,
           memcmp(md, testvec[i].md, testvec[i].mdlen) == 0 ? "passed" : "FAILED");

  }

  // benchmark
  for (i = 0; i < DATALEN; i++) data[i] = i;
  for (i = 0; i < NITER; i++)
    keccak(data, DATALEN, md, 64);

  return 0;
}

