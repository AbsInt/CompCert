/* Printing of modifiers */

typedef struct vba_version_tag {
	unsigned char signature[4];
	const char *name;
	int is_mac;
} vba_version_t;

static const vba_version_t vba_version[10];

int f(int x)
{
  return sizeof(vba_version[0].signature);
}

