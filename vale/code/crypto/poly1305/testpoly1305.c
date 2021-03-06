#include <stdio.h>
#include "gcc_compat.h"
#include <stdint.h> // for uint?_t
#include <string.h> // for memcmp

struct ctxt
{
    uint64_t h0;
    uint64_t h1;
    uint64_t h2;
    uint64_t key_r0;

    uint64_t key_r1;
    uint64_t key_s0;
    uint64_t key_s1;
    uint64_t scratch0;

    uint64_t scratch[24 - 8];
};

// These are the Vale entrypoints
void poly1305(struct ctxt *ctx, const void *inp, uint64_t len);

const uint8_t key[] =
{
  0x85, 0xd6, 0xbe, 0x78, 0x57, 0x55, 0x6d, 0x33, 0x7f, 0x44, 0x52, 0xfe, 0x42, 0xd5, 0x06, 0xa8,
  0x01, 0x03, 0x80, 0x8a, 0xfb, 0x0d, 0xb2, 0xfd, 0x4a, 0xbf, 0xf6, 0xaf, 0x41, 0x49, 0xf5, 0x1b
};

const uint8_t msg[] =
{
  0x43, 0x72, 0x79, 0x70, 0x74, 0x6f, 0x67, 0x72, 0x61, 0x70, 0x68, 0x69, 0x63, 0x20, 0x46, 0x6f,
  0x72, 0x75, 0x6d, 0x20, 0x52, 0x65, 0x73, 0x65, 0x61, 0x72, 0x63, 0x68, 0x20, 0x47, 0x72, 0x6f,
  0x75, 0x70,
  // pad to 48 bytes (extra space filled with junk):
  0x33, 0xbb, 0x77, 0x45, 0xf1, 0x1f, 0x99, 0x88, 0x44, 0x39, 0x48, 0x98, 0x55, 0x41
};

const uint8_t out[] =
{
  0xa8, 0x06, 0x1d, 0xc1, 0x30, 0x51, 0x36, 0xc6, 0xc2, 0x2b, 0x8b, 0xaf, 0x0c, 0x01, 0x27, 0xa9
};

void demo()
{
  struct ctxt ctx;
  memcpy(&(ctx.key_r0), key, sizeof(key));

  poly1305(&ctx, msg, 34);

  if (memcmp(out, &(ctx.h0), sizeof(out)) == 0) {
      printf("poly1305 success\n");
  } else {
      printf("poly1305 failure\n");
  }
}

int main(void)
{
  demo();
  return 0;
}
