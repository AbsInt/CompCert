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

extern void SHA1_init(struct SHA1Context * ctx);
extern void SHA1_add_data(struct SHA1Context * ctx, unsigned char * data,
                          unsigned long len);
extern void SHA1_finish(struct SHA1Context * ctx, unsigned char output[20]);

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

unsigned char * test_input_1 = (unsigned char *) "abc";
unsigned char test_output_1[20] =
{ 0xA9, 0x99, 0x3E, 0x36, 0x47, 0x06, 0x81, 0x6A, 0xBA, 0x3E ,
  0x25, 0x71, 0x78, 0x50, 0xC2, 0x6C, 0x9C, 0xD0, 0xD8, 0x9D };

unsigned char * test_input_2 = (unsigned char *)
  "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
unsigned char test_output_2[20] =
{ 0x84, 0x98, 0x3E, 0x44, 0x1C, 0x3B, 0xD2, 0x6E, 0xBA, 0xAE,
  0x4A, 0xA1, 0xF9, 0x51, 0x29, 0xE5, 0xE5, 0x46, 0x70, 0xF1 };


static void do_bench(int nblocks)
{
  struct SHA1Context ctx;
  unsigned char output[20];
  unsigned char data[64];

  SHA1_init(&ctx);
  for (; nblocks > 0; nblocks--) 
    SHA1_add_data(&ctx, data, 64);
  SHA1_finish(&ctx, output);
}

int main(int argc, char ** argv)
{
  if (argc < 2) {
    do_test(test_input_1, test_output_1);
    do_test(test_input_2, test_output_2);
  } else {
    do_bench(atoi(argv[1]));
  }
  return 0;
}
