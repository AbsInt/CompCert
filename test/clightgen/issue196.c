#include <stdint.h>
#include <stdlib.h>
#include <sys/types.h>


typedef int ASN1_BOOLEAN;
typedef int ASN1_NULL;
typedef struct ASN1_ITEM_st ASN1_ITEM;
typedef struct asn1_object_st ASN1_OBJECT;
typedef struct asn1_pctx_st ASN1_PCTX;
typedef struct asn1_string_st ASN1_BIT_STRING;
typedef struct asn1_string_st ASN1_BMPSTRING;
typedef struct asn1_string_st ASN1_ENUMERATED;
typedef struct asn1_string_st ASN1_GENERALIZEDTIME;
typedef struct asn1_string_st ASN1_GENERALSTRING;
typedef struct asn1_string_st ASN1_IA5STRING;
typedef struct asn1_string_st ASN1_INTEGER;
typedef struct asn1_string_st ASN1_OCTET_STRING;
typedef struct asn1_string_st ASN1_PRINTABLESTRING;
typedef struct asn1_string_st ASN1_STRING;
typedef struct asn1_string_st ASN1_T61STRING;
typedef struct asn1_string_st ASN1_TIME;
typedef struct asn1_string_st ASN1_UNIVERSALSTRING;
typedef struct asn1_string_st ASN1_UTCTIME;
typedef struct asn1_string_st ASN1_UTF8STRING;
typedef struct asn1_string_st ASN1_VISIBLESTRING;

typedef struct AUTHORITY_KEYID_st AUTHORITY_KEYID;
typedef struct DIST_POINT_st DIST_POINT;
typedef struct ISSUING_DIST_POINT_st ISSUING_DIST_POINT;
typedef struct NAME_CONSTRAINTS_st NAME_CONSTRAINTS;
typedef struct X509_POLICY_CACHE_st X509_POLICY_CACHE;
typedef struct X509_POLICY_LEVEL_st X509_POLICY_LEVEL;
typedef struct X509_POLICY_NODE_st X509_POLICY_NODE;
typedef struct X509_POLICY_TREE_st X509_POLICY_TREE;
typedef struct X509_algor_st X509_ALGOR;
typedef struct X509_crl_st X509_CRL;
typedef struct X509_pubkey_st X509_PUBKEY;
typedef struct bignum_ctx BN_CTX;
typedef struct bignum_st BIGNUM;
typedef struct bio_method_st BIO_METHOD;
typedef struct bio_st BIO;
typedef struct bn_gencb_st BN_GENCB;
typedef struct bn_mont_ctx_st BN_MONT_CTX;
typedef struct buf_mem_st BUF_MEM;
typedef struct cbb_st CBB;
typedef struct cbs_st CBS;
typedef struct conf_st CONF;
typedef struct dh_method DH_METHOD;
typedef struct dh_st DH;
typedef struct dsa_method DSA_METHOD;
typedef struct dsa_st DSA;
typedef struct ec_key_st EC_KEY;
typedef struct ecdsa_method_st ECDSA_METHOD;
typedef struct ecdsa_sig_st ECDSA_SIG;
typedef struct engine_st ENGINE;
typedef struct env_md_ctx_st EVP_MD_CTX;
typedef struct env_md_st EVP_MD;
typedef struct evp_aead_st EVP_AEAD;
typedef struct evp_cipher_ctx_st EVP_CIPHER_CTX;
typedef struct evp_cipher_st EVP_CIPHER;
typedef struct evp_pkey_asn1_method_st EVP_PKEY_ASN1_METHOD;
typedef struct evp_pkey_ctx_st EVP_PKEY_CTX;
typedef struct evp_pkey_method_st EVP_PKEY_METHOD;
typedef struct evp_pkey_st EVP_PKEY;
typedef struct hmac_ctx_st HMAC_CTX;
typedef struct md4_state_st MD4_CTX;
typedef struct md5_state_st MD5_CTX;
typedef struct pkcs8_priv_key_info_st PKCS8_PRIV_KEY_INFO;
typedef struct pkcs12_st PKCS12;
typedef struct rand_meth_st RAND_METHOD;
typedef struct rc4_key_st RC4_KEY;
typedef struct rsa_meth_st RSA_METHOD;
typedef struct rsa_st RSA;
typedef struct sha256_state_st SHA256_CTX;
typedef struct sha512_state_st SHA512_CTX;
typedef struct sha_state_st SHA_CTX;
typedef struct ssl_ctx_st SSL_CTX;
typedef struct ssl_st SSL;
typedef struct st_ERR_FNS ERR_FNS;
typedef struct v3_ext_ctx X509V3_CTX;
typedef struct x509_crl_method_st X509_CRL_METHOD;
typedef struct x509_revoked_st X509_REVOKED;
typedef struct x509_st X509;
typedef struct x509_store_ctx_st X509_STORE_CTX;
typedef struct x509_store_st X509_STORE;
typedef void *OPENSSL_BLOCK;
 const EVP_MD *EVP_md4(void);
 const EVP_MD *EVP_md5(void);
 const EVP_MD *EVP_sha1(void);
 const EVP_MD *EVP_sha224(void);
 const EVP_MD *EVP_sha256(void);
 const EVP_MD *EVP_sha384(void);
 const EVP_MD *EVP_sha512(void);



 const EVP_MD *EVP_md5_sha1(void);



 const EVP_MD *EVP_get_digestbynid(int nid);



 const EVP_MD *EVP_get_digestbyobj(const ASN1_OBJECT *obj);
 void EVP_MD_CTX_init(EVP_MD_CTX *ctx);



 EVP_MD_CTX *EVP_MD_CTX_create(void);



 int EVP_MD_CTX_cleanup(EVP_MD_CTX *ctx);


 void EVP_MD_CTX_destroy(EVP_MD_CTX *ctx);



 int EVP_MD_CTX_copy_ex(EVP_MD_CTX *out, const EVP_MD_CTX *in);







 int EVP_DigestInit_ex(EVP_MD_CTX *ctx, const EVP_MD *type,
                                     ENGINE *engine);



 int EVP_DigestInit(EVP_MD_CTX *ctx, const EVP_MD *type);



 int EVP_DigestUpdate(EVP_MD_CTX *ctx, const void *data,
                                    size_t len);
 int EVP_DigestFinal_ex(EVP_MD_CTX *ctx, uint8_t *md_out,
                                      unsigned int *out_size);



 int EVP_DigestFinal(EVP_MD_CTX *ctx, uint8_t *md_out,
                                   unsigned int *out_size);






 int EVP_Digest(const void *data, size_t len, uint8_t *md_out,
                              unsigned int *md_out_size, const EVP_MD *type,
                              ENGINE *impl);
 int EVP_MD_type(const EVP_MD *md);


 const char *EVP_MD_name(const EVP_MD *md);



 uint32_t EVP_MD_flags(const EVP_MD *md);


 size_t EVP_MD_size(const EVP_MD *md);


 size_t EVP_MD_block_size(const EVP_MD *md);
 int EVP_MD_CTX_copy(EVP_MD_CTX *out, const EVP_MD_CTX *in);



 int EVP_add_digest(const EVP_MD *digest);






 const EVP_MD *EVP_MD_CTX_md(const EVP_MD_CTX *ctx);



 unsigned EVP_MD_CTX_size(const EVP_MD_CTX *ctx);



 unsigned EVP_MD_CTX_block_size(const EVP_MD_CTX *ctx);




 int EVP_MD_CTX_type(const EVP_MD_CTX *ctx);


 void EVP_MD_CTX_set_flags(EVP_MD_CTX *ctx, uint32_t flags);



 void EVP_MD_CTX_clear_flags(EVP_MD_CTX *ctx, uint32_t flags);



 uint32_t EVP_MD_CTX_test_flags(const EVP_MD_CTX *ctx,
                                              uint32_t flags);


struct evp_md_pctx_ops;

struct env_md_ctx_st {

  const EVP_MD *digest;

  uint32_t flags;


  void *md_data;



  int (*update)(EVP_MD_CTX *ctx, const void *data, size_t count);



  EVP_PKEY_CTX *pctx;



  const struct evp_md_pctx_ops *pctx_ops;
} ;

 int MD4_Init(MD4_CTX *md4);


 int MD4_Update(MD4_CTX *md4, const void *data, size_t len);




 int MD4_Final(uint8_t *md, MD4_CTX *md4);



 void MD4_Transform(MD4_CTX *md4, const uint8_t *block);

struct md4_state_st {
  uint32_t A, B, C, D;
  uint32_t Nl, Nh;
  uint32_t data[16];
  unsigned int num;
};
 int MD5_Init(MD5_CTX *md5);


 int MD5_Update(MD5_CTX *md5, const void *data, size_t len);




 int MD5_Final(uint8_t *md, MD5_CTX *md5);



 uint8_t *MD5(const uint8_t *data, size_t len, uint8_t *out);



 void MD5_Transform(MD5_CTX *md5, const uint8_t *block);

struct md5_state_st {
  uint32_t A, B, C, D;
  uint32_t Nl, Nh;
  uint32_t data[16];
  unsigned int num;
};
struct cbs_st {
  const uint8_t *data;
  size_t len;
};



 void CBS_init(CBS *cbs, const uint8_t *data, size_t len);



 int CBS_skip(CBS *cbs, size_t len);


 const uint8_t *CBS_data(const CBS *cbs);


 size_t CBS_len(const CBS *cbs);






 int CBS_stow(const CBS *cbs, uint8_t **out_ptr, size_t *out_len);
 int CBS_strdup(const CBS *cbs, char **out_ptr);



 int CBS_contains_zero_byte(const CBS *cbs);




 int CBS_mem_equal(const CBS *cbs, const uint8_t *data,
                                 size_t len);



 int CBS_get_u8(CBS *cbs, uint8_t *out);



 int CBS_get_u16(CBS *cbs, uint16_t *out);



 int CBS_get_u24(CBS *cbs, uint32_t *out);



 int CBS_get_u32(CBS *cbs, uint32_t *out);



 int CBS_get_bytes(CBS *cbs, CBS *out, size_t len);




 int CBS_get_u8_length_prefixed(CBS *cbs, CBS *out);




 int CBS_get_u16_length_prefixed(CBS *cbs, CBS *out);




 int CBS_get_u24_length_prefixed(CBS *cbs, CBS *out);
 int CBS_get_asn1(CBS *cbs, CBS *out, unsigned tag_value);



 int CBS_get_asn1_element(CBS *cbs, CBS *out, unsigned tag_value);






 int CBS_peek_asn1_tag(const CBS *cbs, unsigned tag_value);
 int CBS_get_any_asn1_element(CBS *cbs, CBS *out,
                                            unsigned *out_tag,
                                            size_t *out_header_len);





 int CBS_get_asn1_uint64(CBS *cbs, uint64_t *out);






 int CBS_get_optional_asn1(CBS *cbs, CBS *out, int *out_present,
                                         unsigned tag);







 int CBS_get_optional_asn1_octet_string(CBS *cbs, CBS *out,
                                                      int *out_present,
                                                      unsigned tag);






 int CBS_get_optional_asn1_uint64(CBS *cbs, uint64_t *out,
                                                unsigned tag,
                                                uint64_t default_value);






 int CBS_get_optional_asn1_bool(CBS *cbs, int *out, unsigned tag,
                                              int default_value);
struct cbb_buffer_st {
  uint8_t *buf;
  size_t len;
  size_t cap;
  char can_resize;

};

struct cbb_st {
  struct cbb_buffer_st *base;


  size_t offset;

  struct cbb_st *child;


  uint8_t pending_len_len;
  char pending_is_asn1;


  char is_top_level;
};




 int CBB_init(CBB *cbb, size_t initial_capacity);




 int CBB_init_fixed(CBB *cbb, uint8_t *buf, size_t len);




 void CBB_cleanup(CBB *cbb);
 int CBB_finish(CBB *cbb, uint8_t **out_data, size_t *out_len);




 int CBB_flush(CBB *cbb);




 int CBB_add_u8_length_prefixed(CBB *cbb, CBB *out_contents);




 int CBB_add_u16_length_prefixed(CBB *cbb, CBB *out_contents);




 int CBB_add_u24_length_prefixed(CBB *cbb, CBB *out_contents);






 int CBB_add_asn1(CBB *cbb, CBB *out_contents, uint8_t tag);



 int CBB_add_bytes(CBB *cbb, const uint8_t *data, size_t len);





 int CBB_add_space(CBB *cbb, uint8_t **out_data, size_t len);



 int CBB_add_u8(CBB *cbb, uint8_t value);



 int CBB_add_u16(CBB *cbb, uint16_t value);



 int CBB_add_u24(CBB *cbb, uint32_t value);




 int CBB_add_asn1_uint64(CBB *cbb, uint64_t value);
 ASN1_OBJECT *OBJ_dup(const ASN1_OBJECT *obj);



 int OBJ_cmp(const ASN1_OBJECT *a, const ASN1_OBJECT *b);






 int OBJ_obj2nid(const ASN1_OBJECT *obj);



 int OBJ_cbs2nid(const CBS *cbs);



 int OBJ_sn2nid(const char *short_name);



 int OBJ_ln2nid(const char *long_name);




 int OBJ_txt2nid(const char *s);






 const ASN1_OBJECT *OBJ_nid2obj(int nid);


 const char *OBJ_nid2sn(int nid);


 const char *OBJ_nid2ln(int nid);



 int OBJ_nid2cbb(CBB *out, int nid);
 ASN1_OBJECT *OBJ_txt2obj(const char *s, int dont_search_names);
 int OBJ_obj2txt(char *out, int out_len, const ASN1_OBJECT *obj,
                               int dont_return_name);






 int OBJ_create(const char *oid, const char *short_name,
                              const char *long_name);
 int OBJ_find_sigid_algs(int sign_nid, int *out_digest_nid,
                                       int *out_pkey_nid);






 int OBJ_find_sigid_by_algs(int *out_sign_nid, int digest_nid,
                                          int pkey_nid);
 int SHA1_Init(SHA_CTX *sha);


 int SHA1_Update(SHA_CTX *sha, const void *data, size_t len);




 int SHA1_Final(uint8_t *md, SHA_CTX *sha);




 uint8_t *SHA1(const uint8_t *data, size_t len, uint8_t *out);



 void SHA1_Transform(SHA_CTX *sha, const uint8_t *block);

struct sha_state_st {
  uint32_t h0, h1, h2, h3, h4;
  uint32_t Nl, Nh;
  uint32_t data[16];
  unsigned int num;
};
 int SHA224_Init(SHA256_CTX *sha);


 int SHA224_Update(SHA256_CTX *sha, const void *data, size_t len);



 int SHA224_Final(uint8_t *md, SHA256_CTX *sha);




 uint8_t *SHA224(const uint8_t *data, size_t len, uint8_t *out);
 int SHA256_Init(SHA256_CTX *sha);


 int SHA256_Update(SHA256_CTX *sha, const void *data, size_t len);



 int SHA256_Final(uint8_t *md, SHA256_CTX *sha);




 uint8_t *SHA256(const uint8_t *data, size_t len, uint8_t *out);



 void SHA256_Transform(SHA256_CTX *sha, const uint8_t *data);

struct sha256_state_st {
  uint32_t h[8];
  uint32_t Nl, Nh;
  uint32_t data[16];
  unsigned int num, md_len;
};
 int SHA384_Init(SHA512_CTX *sha);


 int SHA384_Update(SHA512_CTX *sha, const void *data, size_t len);



 int SHA384_Final(uint8_t *md, SHA512_CTX *sha);




 uint8_t *SHA384(const uint8_t *data, size_t len, uint8_t *out);



 void SHA384_Transform(SHA512_CTX *sha, const uint8_t *data);
 int SHA512_Init(SHA512_CTX *sha);


 int SHA512_Update(SHA512_CTX *sha, const void *data, size_t len);



 int SHA512_Final(uint8_t *md, SHA512_CTX *sha);




 uint8_t *SHA512(const uint8_t *data, size_t len, uint8_t *out);



 void SHA512_Transform(SHA512_CTX *sha, const uint8_t *data);

struct sha512_state_st {
  uint64_t h[8];
  uint64_t Nl, Nh;
  union {
    uint64_t d[16];
    uint8_t p[128];
  } u;
  unsigned int num, md_len;
};

struct env_md_st {


  int type;


  unsigned md_size;


  uint32_t flags;



  int (*init)(EVP_MD_CTX *ctx);


  int (*update)(EVP_MD_CTX *ctx, const void *data, size_t count);


  int (*final)(EVP_MD_CTX *ctx, uint8_t *out);


  unsigned block_size;


  unsigned ctx_size;
};




struct evp_md_pctx_ops {


  void (*free) (EVP_PKEY_CTX *pctx);



  EVP_PKEY_CTX* (*dup) (EVP_PKEY_CTX *pctx);



  int (*begin_digest) (EVP_MD_CTX *ctx);
};


static int md4_init(EVP_MD_CTX *ctx) { return MD4_Init(ctx->md_data); }

static int md4_update(EVP_MD_CTX *ctx, const void *data, size_t count) {
  return MD4_Update(ctx->md_data, data, count);
}

static int md4_final(EVP_MD_CTX *ctx, unsigned char *out) {
  return MD4_Final(out, ctx->md_data);
}

static const EVP_MD md4_md = {
    257, 16, 0 , md4_init,
    md4_update, md4_final, 64 , sizeof(MD4_CTX),
};

const EVP_MD *EVP_md4(void) { return &md4_md; }


static int md5_init(EVP_MD_CTX *ctx) { return MD5_Init(ctx->md_data); }

static int md5_update(EVP_MD_CTX *ctx, const void *data, size_t count) {
  return MD5_Update(ctx->md_data, data, count);
}

static int md5_final(EVP_MD_CTX *ctx, unsigned char *out) {
  return MD5_Final(out, ctx->md_data);
}

static const EVP_MD md5_md = {
    4, 16, 0 , md5_init,
    md5_update, md5_final, 64 , sizeof(MD5_CTX),
};

const EVP_MD *EVP_md5(void) { return &md5_md; }


static int sha1_init(EVP_MD_CTX *ctx) { return SHA1_Init(ctx->md_data); }

static int sha1_update(EVP_MD_CTX *ctx, const void *data, size_t count) {
  return SHA1_Update(ctx->md_data, data, count);
}

static int sha1_final(EVP_MD_CTX *ctx, unsigned char *md) {
  return SHA1_Final(md, ctx->md_data);
}

static const EVP_MD sha1_md = {
    64, 20, 0 , sha1_init,
    sha1_update, sha1_final, 64 , sizeof(SHA_CTX),
};

const EVP_MD *EVP_sha1(void) { return &sha1_md; }


static int sha224_init(EVP_MD_CTX *ctx) { return SHA224_Init(ctx->md_data); }

static int sha224_update(EVP_MD_CTX *ctx, const void *data, size_t count) {
  return SHA224_Update(ctx->md_data, data, count);
}

static int sha224_final(EVP_MD_CTX *ctx, unsigned char *md) {
  return SHA224_Final(md, ctx->md_data);
}

static const EVP_MD sha224_md = {
    675, 28, 0 ,
    sha224_init, sha224_update, sha224_final,
    64 , sizeof(SHA256_CTX),
};

const EVP_MD *EVP_sha224(void) { return &sha224_md; }


static int sha256_init(EVP_MD_CTX *ctx) { return SHA256_Init(ctx->md_data); }

static int sha256_update(EVP_MD_CTX *ctx, const void *data, size_t count) {
  return SHA256_Update(ctx->md_data, data, count);
}

static int sha256_final(EVP_MD_CTX *ctx, unsigned char *md) {
  return SHA256_Final(md, ctx->md_data);
}

static const EVP_MD sha256_md = {
    672, 32, 0 ,
    sha256_init, sha256_update, sha256_final,
    64 , sizeof(SHA256_CTX),
};

const EVP_MD *EVP_sha256(void) { return &sha256_md; }


static int sha384_init(EVP_MD_CTX *ctx) { return SHA384_Init(ctx->md_data); }

static int sha384_update(EVP_MD_CTX *ctx, const void *data, size_t count) {
  return SHA384_Update(ctx->md_data, data, count);
}

static int sha384_final(EVP_MD_CTX *ctx, unsigned char *md) {
  return SHA384_Final(md, ctx->md_data);
}

static const EVP_MD sha384_md = {
    673, 48, 0 ,
    sha384_init, sha384_update, sha384_final,
    128 , sizeof(SHA512_CTX),
};

const EVP_MD *EVP_sha384(void) { return &sha384_md; }


static int sha512_init(EVP_MD_CTX *ctx) { return SHA512_Init(ctx->md_data); }

static int sha512_update(EVP_MD_CTX *ctx, const void *data, size_t count) {
  return SHA512_Update(ctx->md_data, data, count);
}

static int sha512_final(EVP_MD_CTX *ctx, unsigned char *md) {
  return SHA512_Final(md, ctx->md_data);
}

static const EVP_MD sha512_md = {
    674, 64, 0 ,
    sha512_init, sha512_update, sha512_final,
    128 , sizeof(SHA512_CTX),
};

const EVP_MD *EVP_sha512(void) { return &sha512_md; }


typedef struct {
  MD5_CTX md5;
  SHA_CTX sha1;
} MD5_SHA1_CTX;

static int md5_sha1_init(EVP_MD_CTX *md_ctx) {
  MD5_SHA1_CTX *ctx = md_ctx->md_data;
  return MD5_Init(&ctx->md5) && SHA1_Init(&ctx->sha1);
}

static int md5_sha1_update(EVP_MD_CTX *md_ctx, const void *data, size_t count) {
  MD5_SHA1_CTX *ctx = md_ctx->md_data;
  return MD5_Update(&ctx->md5, data, count) && SHA1_Update(&ctx->sha1, data, count);
}

static int md5_sha1_final(EVP_MD_CTX *md_ctx, unsigned char *out) {
  MD5_SHA1_CTX *ctx = md_ctx->md_data;
  if (!MD5_Final(out, &ctx->md5) ||
      !SHA1_Final(out + 16, &ctx->sha1)) {
    return 0;
  }
  return 1;
}

static const EVP_MD md5_sha1_md = {
    114,
    16 + 20,
    0 ,
    md5_sha1_init,
    md5_sha1_update,
    md5_sha1_final,
    64 ,
    sizeof(MD5_SHA1_CTX),
};

const EVP_MD *EVP_md5_sha1(void) { return &md5_sha1_md; }


struct nid_to_digest {
  int nid;
  const EVP_MD* (*md_func)(void);
};

static const struct nid_to_digest nid_to_digest_mapping[] = {
  { 4, EVP_md5 },
  { 64, EVP_sha1 },
  { 675, EVP_sha224 },
  { 672, EVP_sha256 },
  { 673, EVP_sha384 },
  { 674, EVP_sha512 },
  { 114, EVP_md5_sha1 },
  { 66, EVP_sha1 },
  { 113, EVP_sha1 },
  { 416, EVP_sha1 },
  { 8, EVP_md5 },
  { 65, EVP_sha1 },
  { 671, EVP_sha224 },
  { 668, EVP_sha256 },
  { 669, EVP_sha384 },
  { 670, EVP_sha512 },
};

const EVP_MD* EVP_get_digestbynid(int nid) {
  unsigned i;

  for (i = 0; i < sizeof(nid_to_digest_mapping) / sizeof(struct nid_to_digest);
       i++) {
    if (nid_to_digest_mapping[i].nid == nid) {
      return nid_to_digest_mapping[i].md_func();
    }
  }

  return 
        ((void *)0)
            ;
}

const EVP_MD* EVP_get_digestbyobj(const ASN1_OBJECT *obj) {
  return EVP_get_digestbynid(OBJ_obj2nid(obj));
}
