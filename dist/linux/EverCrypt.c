/* MIT License
 *
 * Copyright (c) 2016-2020 INRIA, CMU and Microsoft Corporation
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */


#include "EverCrypt.h"

u32 EverCrypt_random_init()
{
  if (EverCrypt_AutoConfig2_wants_openssl())
  {
    return EverCrypt_OpenSSL_random_init();
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "ERROR: inconsistent configuration (random_init)");
    KRML_HOST_EXIT(255U);
  }
}

void EverCrypt_random_sample(u32 len, u8 *out1)
{
  if (EverCrypt_AutoConfig2_wants_openssl())
  {
    EverCrypt_OpenSSL_random_sample(len, out1);
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "ERROR: inconsistent configuration (random_sample)");
    KRML_HOST_EXIT(255U);
  }
}

void EverCrypt_random_cleanup()
{
  if (!EverCrypt_AutoConfig2_wants_openssl())
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "ERROR: inconsistent configuration (random_cleanup)");
    KRML_HOST_EXIT(255U);
  }
}

typedef struct EverCrypt_aes128_key_s_s
{
  EverCrypt_aes128_key_s_tags tag;
  union {
    FStar_Dyn_dyn case_AES128_OPENSSL;
    FStar_Dyn_dyn case_AES128_BCRYPT;
    struct 
    {
      u8 *w;
      u8 *sbox;
    }
    case_AES128_VALE;
    struct 
    {
      u8 *w;
      u8 *sbox;
    }
    case_AES128_HACL;
  }
  ;
}
EverCrypt_aes128_key_s;

bool EverCrypt_uu___is_AES128_OPENSSL(EverCrypt_aes128_key_s projectee)
{
  if (projectee.tag == EverCrypt_AES128_OPENSSL)
  {
    return true;
  }
  else
  {
    return false;
  }
}

FStar_Dyn_dyn EverCrypt___proj__AES128_OPENSSL__item__st(EverCrypt_aes128_key_s projectee)
{
  if (projectee.tag == EverCrypt_AES128_OPENSSL)
  {
    return projectee.case_AES128_OPENSSL;
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool EverCrypt_uu___is_AES128_BCRYPT(EverCrypt_aes128_key_s projectee)
{
  if (projectee.tag == EverCrypt_AES128_BCRYPT)
  {
    return true;
  }
  else
  {
    return false;
  }
}

FStar_Dyn_dyn EverCrypt___proj__AES128_BCRYPT__item__st(EverCrypt_aes128_key_s projectee)
{
  if (projectee.tag == EverCrypt_AES128_BCRYPT)
  {
    return projectee.case_AES128_BCRYPT;
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool EverCrypt_uu___is_AES128_VALE(EverCrypt_aes128_key_s projectee)
{
  if (projectee.tag == EverCrypt_AES128_VALE)
  {
    return true;
  }
  else
  {
    return false;
  }
}

u8 *EverCrypt___proj__AES128_VALE__item__w(EverCrypt_aes128_key_s projectee)
{
  if (projectee.tag == EverCrypt_AES128_VALE)
  {
    return projectee.case_AES128_VALE.w;
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

u8 *EverCrypt___proj__AES128_VALE__item__sbox(EverCrypt_aes128_key_s projectee)
{
  if (projectee.tag == EverCrypt_AES128_VALE)
  {
    return projectee.case_AES128_VALE.sbox;
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool EverCrypt_uu___is_AES128_HACL(EverCrypt_aes128_key_s projectee)
{
  if (projectee.tag == EverCrypt_AES128_HACL)
  {
    return true;
  }
  else
  {
    return false;
  }
}

u8 *EverCrypt___proj__AES128_HACL__item__w(EverCrypt_aes128_key_s projectee)
{
  if (projectee.tag == EverCrypt_AES128_HACL)
  {
    return projectee.case_AES128_HACL.w;
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

u8 *EverCrypt___proj__AES128_HACL__item__sbox(EverCrypt_aes128_key_s projectee)
{
  if (projectee.tag == EverCrypt_AES128_HACL)
  {
    return projectee.case_AES128_HACL.sbox;
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

KRML_DEPRECATED("Please use EverCrypt_CTR.h (from C) or EverCrypt.CTR.fsti (from F*) ")

EverCrypt_aes128_key_s *EverCrypt_aes128_create(u8 *k1)
{
  bool ite;
  if (EverCrypt_AutoConfig2_wants_vale())
  {
    ite = EverCrypt_AutoConfig2_has_aesni();
  }
  else
  {
    ite = false;
  }
  {
    EverCrypt_aes128_key_s st;
    if (ite)
    {
      u8 *w1 = KRML_HOST_CALLOC((u32)176U, sizeof (u8));
      u8 *sbox = KRML_HOST_CALLOC((u32)256U, sizeof (u8));
      aes128_key_expansion_sbox(k1, w1, sbox);
      st =
        (
          (EverCrypt_aes128_key_s){
            .tag = EverCrypt_AES128_VALE,
            { .case_AES128_VALE = { .w = w1, .sbox = sbox } }
          }
        );
    }
    else if (EverCrypt_AutoConfig2_wants_hacl())
    {
      u8 *w1 = KRML_HOST_CALLOC((u32)176U, sizeof (u8));
      u8 *sbox = KRML_HOST_CALLOC((u32)256U, sizeof (u8));
      EverCrypt_Hacl_aes128_mk_sbox(sbox);
      EverCrypt_Hacl_aes128_keyExpansion(k1, w1, sbox);
      st =
        (
          (EverCrypt_aes128_key_s){
            .tag = EverCrypt_AES128_HACL,
            { .case_AES128_HACL = { .w = w1, .sbox = sbox } }
          }
        );
    }
    else
    {
      st = KRML_EABORT(EverCrypt_aes128_key_s, "ERROR: inconsistent configuration (aes128_create)");
    }
    KRML_CHECK_SIZE(sizeof (EverCrypt_aes128_key_s), (u32)1U);
    {
      EverCrypt_aes128_key_s *buf = KRML_HOST_MALLOC(sizeof (EverCrypt_aes128_key_s));
      buf[0U] = st;
      return buf;
    }
  }
}

KRML_DEPRECATED("Please use EverCrypt_CTR.h (from C) or EverCrypt.CTR.fsti (from F*) ")

void EverCrypt_aes128_compute(EverCrypt_aes128_key_s *k1, u8 *plain, u8 *cipher)
{
  EverCrypt_aes128_key_s k2 = *k1;
  if (true && EverCrypt_uu___is_AES128_VALE(k2))
  {
    if (k2.tag == EverCrypt_AES128_VALE)
    {
      u8 *sbox = k2.case_AES128_VALE.sbox;
      u8 *w1 = k2.case_AES128_VALE.w;
      aes128_encrypt_one_block(cipher, plain, w1, sbox);
    }
    else
    {
      KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "unreachable (pattern matches are exhaustive in F*)");
      KRML_HOST_EXIT(255U);
    }
  }
  else if (true && EverCrypt_uu___is_AES128_HACL(k2))
  {
    if (k2.tag == EverCrypt_AES128_HACL)
    {
      u8 *sbox = k2.case_AES128_HACL.sbox;
      u8 *w1 = k2.case_AES128_HACL.w;
      EverCrypt_Hacl_aes128_cipher(cipher, plain, w1, sbox);
    }
    else
    {
      KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "unreachable (pattern matches are exhaustive in F*)");
      KRML_HOST_EXIT(255U);
    }
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "ERROR: inconsistent configuration (aes128_compute)");
    KRML_HOST_EXIT(255U);
  }
}

KRML_DEPRECATED("Please use EverCrypt_CTR.h (from C) or EverCrypt.CTR.fsti (from F*) ")

void EverCrypt_aes128_free(EverCrypt_aes128_key_s *pk)
{
  EverCrypt_aes128_key_s k1 = *pk;
  if (true && EverCrypt_uu___is_AES128_VALE(k1))
  {
    if (k1.tag == EverCrypt_AES128_VALE)
    {
      u8 *sbox = k1.case_AES128_VALE.sbox;
      u8 *w1 = k1.case_AES128_VALE.w;
      KRML_HOST_FREE(w1);
      KRML_HOST_FREE(sbox);
    }
    else
    {
      KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "unreachable (pattern matches are exhaustive in F*)");
      KRML_HOST_EXIT(255U);
    }
  }
  else if (true && EverCrypt_uu___is_AES128_HACL(k1))
  {
    if (k1.tag == EverCrypt_AES128_HACL)
    {
      u8 *sbox = k1.case_AES128_HACL.sbox;
      u8 *w1 = k1.case_AES128_HACL.w;
      KRML_HOST_FREE(w1);
      KRML_HOST_FREE(sbox);
    }
    else
    {
      KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "unreachable (pattern matches are exhaustive in F*)");
      KRML_HOST_EXIT(255U);
    }
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "ERROR: inconsistent configuration (aes128_free)");
    KRML_HOST_EXIT(255U);
  }
  KRML_HOST_FREE(pk);
}

typedef struct EverCrypt_aes256_key_s_s
{
  EverCrypt_aes256_key_s_tags tag;
  union {
    FStar_Dyn_dyn case_AES256_OPENSSL;
    FStar_Dyn_dyn case_AES256_BCRYPT;
    struct 
    {
      u8 *w;
      u8 *sbox;
    }
    case_AES256_HACL;
  }
  ;
}
EverCrypt_aes256_key_s;

bool EverCrypt_uu___is_AES256_OPENSSL(EverCrypt_aes256_key_s projectee)
{
  if (projectee.tag == EverCrypt_AES256_OPENSSL)
  {
    return true;
  }
  else
  {
    return false;
  }
}

FStar_Dyn_dyn EverCrypt___proj__AES256_OPENSSL__item__st(EverCrypt_aes256_key_s projectee)
{
  if (projectee.tag == EverCrypt_AES256_OPENSSL)
  {
    return projectee.case_AES256_OPENSSL;
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool EverCrypt_uu___is_AES256_BCRYPT(EverCrypt_aes256_key_s projectee)
{
  if (projectee.tag == EverCrypt_AES256_BCRYPT)
  {
    return true;
  }
  else
  {
    return false;
  }
}

FStar_Dyn_dyn EverCrypt___proj__AES256_BCRYPT__item__st(EverCrypt_aes256_key_s projectee)
{
  if (projectee.tag == EverCrypt_AES256_BCRYPT)
  {
    return projectee.case_AES256_BCRYPT;
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool EverCrypt_uu___is_AES256_HACL(EverCrypt_aes256_key_s projectee)
{
  if (projectee.tag == EverCrypt_AES256_HACL)
  {
    return true;
  }
  else
  {
    return false;
  }
}

u8 *EverCrypt___proj__AES256_HACL__item__w(EverCrypt_aes256_key_s projectee)
{
  if (projectee.tag == EverCrypt_AES256_HACL)
  {
    return projectee.case_AES256_HACL.w;
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

u8 *EverCrypt___proj__AES256_HACL__item__sbox(EverCrypt_aes256_key_s projectee)
{
  if (projectee.tag == EverCrypt_AES256_HACL)
  {
    return projectee.case_AES256_HACL.sbox;
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

KRML_DEPRECATED("Please use EverCrypt_CTR.h (from C) or EverCrypt.CTR.fsti (from F*) ")

EverCrypt_aes256_key_s *EverCrypt_aes256_create(u8 *k1)
{
  EverCrypt_aes256_key_s st;
  if (EverCrypt_AutoConfig2_wants_hacl())
  {
    u8 *w1 = KRML_HOST_CALLOC((u32)240U, sizeof (u8));
    u8 *sbox = KRML_HOST_CALLOC((u32)256U, sizeof (u8));
    EverCrypt_Hacl_aes256_mk_sbox(sbox);
    EverCrypt_Hacl_aes256_keyExpansion(k1, w1, sbox);
    st =
      (
        (EverCrypt_aes256_key_s){
          .tag = EverCrypt_AES256_HACL,
          { .case_AES256_HACL = { .w = w1, .sbox = sbox } }
        }
      );
  }
  else
  {
    st = KRML_EABORT(EverCrypt_aes256_key_s, "ERROR: inconsistent configuration (aes256_create)");
  }
  KRML_CHECK_SIZE(sizeof (EverCrypt_aes256_key_s), (u32)1U);
  {
    EverCrypt_aes256_key_s *buf = KRML_HOST_MALLOC(sizeof (EverCrypt_aes256_key_s));
    buf[0U] = st;
    return buf;
  }
}

KRML_DEPRECATED("Please use EverCrypt_CTR.h (from C) or EverCrypt.CTR.fsti (from F*) ")

void EverCrypt_aes256_compute(EverCrypt_aes256_key_s *k1, u8 *plain, u8 *cipher)
{
  EverCrypt_aes256_key_s k2 = *k1;
  if (true && EverCrypt_uu___is_AES256_HACL(k2))
  {
    if (k2.tag == EverCrypt_AES256_HACL)
    {
      u8 *sbox = k2.case_AES256_HACL.sbox;
      u8 *w1 = k2.case_AES256_HACL.w;
      EverCrypt_Hacl_aes256_cipher(cipher, plain, w1, sbox);
    }
    else
    {
      KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "unreachable (pattern matches are exhaustive in F*)");
      KRML_HOST_EXIT(255U);
    }
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "ERROR: inconsistent configuration (aes256_compute)");
    KRML_HOST_EXIT(255U);
  }
}

KRML_DEPRECATED("Please use EverCrypt_CTR.h (from C) or EverCrypt.CTR.fsti (from F*) ")

void EverCrypt_aes256_free(EverCrypt_aes256_key_s *pk)
{
  EverCrypt_aes256_key_s k1 = *pk;
  if (true && EverCrypt_uu___is_AES256_HACL(k1))
  {
    if (k1.tag == EverCrypt_AES256_HACL)
    {
      u8 *sbox = k1.case_AES256_HACL.sbox;
      u8 *w1 = k1.case_AES256_HACL.w;
      KRML_HOST_FREE(w1);
      KRML_HOST_FREE(sbox);
    }
    else
    {
      KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "unreachable (pattern matches are exhaustive in F*)");
      KRML_HOST_EXIT(255U);
    }
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "ERROR: inconsistent configuration (aes256_free)");
    KRML_HOST_EXIT(255U);
  }
  KRML_HOST_FREE(pk);
}

KRML_DEPRECATED("Please use EverCrypt_AEAD.h (from C) or EverCrypt.AEAD.fsti (from F*) ")

void
EverCrypt_aes128_gcm_encrypt(
  u8 *key,
  u8 *iv,
  u8 *ad,
  u32 adlen,
  u8 *plaintext,
  u32 len,
  u8 *cipher,
  u8 *tag
)
{
  bool ite;
  if (EverCrypt_AutoConfig2_wants_vale())
  {
    ite = EverCrypt_AutoConfig2_has_aesni();
  }
  else
  {
    ite = false;
  }
  if (ite)
  {
    u8 expanded[176U] = { 0U };
    old_aes128_key_expansion(key, expanded);
    {
      u8 iv_[16U] = { 0U };
      KRML_CHECK_SIZE(sizeof (u8), (len + (u32)15U) / (u32)16U * (u32)16U);
      {
        u8 plaintext_[(len + (u32)15U) / (u32)16U * (u32)16U];
        memset(plaintext_, 0U, (len + (u32)15U) / (u32)16U * (u32)16U * sizeof plaintext_[0U]);
        KRML_CHECK_SIZE(sizeof (u8), (len + (u32)15U) / (u32)16U * (u32)16U);
        {
          u8 cipher_[(len + (u32)15U) / (u32)16U * (u32)16U];
          memset(cipher_, 0U, (len + (u32)15U) / (u32)16U * (u32)16U * sizeof cipher_[0U]);
          KRML_CHECK_SIZE(sizeof (u8), (adlen + (u32)15U) / (u32)16U * (u32)16U);
          {
            u8 ad_[(adlen + (u32)15U) / (u32)16U * (u32)16U];
            memset(ad_, 0U, (adlen + (u32)15U) / (u32)16U * (u32)16U * sizeof ad_[0U]);
            memcpy(iv_, iv, (u32)12U * sizeof iv[0U]);
            memcpy(plaintext_, plaintext, len * sizeof plaintext[0U]);
            memcpy(ad_, ad, adlen * sizeof ad[0U]);
            {
              gcm_args
              b =
                {
                  .plain = plaintext_, .plain_len = (u64)len, .aad = ad_, .aad_len = (u64)adlen,
                  .iv = iv_, .expanded_key = expanded, .cipher = cipher_, .tag = tag
                };
              old_gcm128_encrypt(&b);
              memcpy(cipher, cipher_, len * sizeof cipher_[0U]);
            }
          }
        }
      }
    }
  }
  else if (EverCrypt_AutoConfig2_wants_openssl())
  {
    EverCrypt_OpenSSL_aes128_gcm_encrypt(key, iv, ad, adlen, plaintext, len, cipher, tag);
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "ERROR: inconsistent configuration (aes128_gcm_encrypt)");
    KRML_HOST_EXIT(255U);
  }
}

KRML_DEPRECATED("Please use EverCrypt_AEAD.h (from C) or EverCrypt.AEAD.fsti (from F*) ")

u32
EverCrypt_aes128_gcm_decrypt(
  u8 *key,
  u8 *iv,
  u8 *ad,
  u32 adlen,
  u8 *plaintext,
  u32 len,
  u8 *cipher,
  u8 *tag
)
{
  bool ite;
  if (EverCrypt_AutoConfig2_wants_vale())
  {
    ite = EverCrypt_AutoConfig2_has_aesni();
  }
  else
  {
    ite = false;
  }
  if (ite)
  {
    u8 expanded[176U] = { 0U };
    old_aes128_key_expansion(key, expanded);
    {
      u8 iv_[16U] = { 0U };
      KRML_CHECK_SIZE(sizeof (u8), (len + (u32)15U) / (u32)16U * (u32)16U);
      {
        u8 plaintext_[(len + (u32)15U) / (u32)16U * (u32)16U];
        memset(plaintext_, 0U, (len + (u32)15U) / (u32)16U * (u32)16U * sizeof plaintext_[0U]);
        KRML_CHECK_SIZE(sizeof (u8), (len + (u32)15U) / (u32)16U * (u32)16U);
        {
          u8 cipher_[(len + (u32)15U) / (u32)16U * (u32)16U];
          memset(cipher_, 0U, (len + (u32)15U) / (u32)16U * (u32)16U * sizeof cipher_[0U]);
          KRML_CHECK_SIZE(sizeof (u8), (adlen + (u32)15U) / (u32)16U * (u32)16U);
          {
            u8 ad_[(adlen + (u32)15U) / (u32)16U * (u32)16U];
            memset(ad_, 0U, (adlen + (u32)15U) / (u32)16U * (u32)16U * sizeof ad_[0U]);
            memcpy(iv_, iv, (u32)12U * sizeof iv[0U]);
            memcpy(cipher_, cipher, len * sizeof cipher[0U]);
            memcpy(ad_, ad, adlen * sizeof ad[0U]);
            {
              gcm_args
              b =
                {
                  .plain = cipher_, .plain_len = (u64)len, .aad = ad_, .aad_len = (u64)adlen,
                  .iv = iv_, .expanded_key = expanded, .cipher = plaintext_, .tag = tag
                };
              u32 ret = old_gcm128_decrypt(&b);
              memcpy(plaintext, plaintext_, len * sizeof plaintext_[0U]);
              if (ret == (u32)0U)
              {
                return (u32)1U;
              }
              else
              {
                return (u32)0U;
              }
            }
          }
        }
      }
    }
  }
  else if (EverCrypt_AutoConfig2_wants_openssl())
  {
    return EverCrypt_OpenSSL_aes128_gcm_decrypt(key, iv, ad, adlen, plaintext, len, cipher, tag);
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "ERROR: inconsistent configuration (aes128_gcm_decrypt)");
    KRML_HOST_EXIT(255U);
  }
}

KRML_DEPRECATED("Please use EverCrypt_AEAD.h (from C) or EverCrypt.AEAD.fsti (from F*) ")

void
EverCrypt_aes256_gcm_encrypt(
  u8 *key,
  u8 *iv,
  u8 *ad,
  u32 adlen,
  u8 *plaintext,
  u32 len,
  u8 *cipher,
  u8 *tag
)
{
  bool ite;
  if (EverCrypt_AutoConfig2_wants_vale())
  {
    ite = EverCrypt_AutoConfig2_has_aesni();
  }
  else
  {
    ite = false;
  }
  if (ite)
  {
    u8 expanded[240U] = { 0U };
    old_aes256_key_expansion(key, expanded);
    {
      u8 iv_[16U] = { 0U };
      KRML_CHECK_SIZE(sizeof (u8), (len + (u32)15U) / (u32)16U * (u32)16U);
      {
        u8 plaintext_[(len + (u32)15U) / (u32)16U * (u32)16U];
        memset(plaintext_, 0U, (len + (u32)15U) / (u32)16U * (u32)16U * sizeof plaintext_[0U]);
        KRML_CHECK_SIZE(sizeof (u8), (len + (u32)15U) / (u32)16U * (u32)16U);
        {
          u8 cipher_[(len + (u32)15U) / (u32)16U * (u32)16U];
          memset(cipher_, 0U, (len + (u32)15U) / (u32)16U * (u32)16U * sizeof cipher_[0U]);
          KRML_CHECK_SIZE(sizeof (u8), (adlen + (u32)15U) / (u32)16U * (u32)16U);
          {
            u8 ad_[(adlen + (u32)15U) / (u32)16U * (u32)16U];
            memset(ad_, 0U, (adlen + (u32)15U) / (u32)16U * (u32)16U * sizeof ad_[0U]);
            memcpy(iv_, iv, (u32)12U * sizeof iv[0U]);
            memcpy(plaintext_, plaintext, len * sizeof plaintext[0U]);
            memcpy(ad_, ad, adlen * sizeof ad[0U]);
            {
              gcm_args
              b =
                {
                  .plain = plaintext_, .plain_len = (u64)len, .aad = ad_, .aad_len = (u64)adlen,
                  .iv = iv_, .expanded_key = expanded, .cipher = cipher_, .tag = tag
                };
              old_gcm256_encrypt(&b);
              memcpy(cipher, cipher_, len * sizeof cipher_[0U]);
            }
          }
        }
      }
    }
  }
  else if (EverCrypt_AutoConfig2_wants_openssl())
  {
    EverCrypt_OpenSSL_aes256_gcm_encrypt(key, iv, ad, adlen, plaintext, len, cipher, tag);
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "ERROR: inconsistent configuration (aes256_gcm_encrypt)");
    KRML_HOST_EXIT(255U);
  }
}

KRML_DEPRECATED("Please use EverCrypt_AEAD.h (from C) or EverCrypt.AEAD.fsti (from F*) ")

u32
EverCrypt_aes256_gcm_decrypt(
  u8 *key,
  u8 *iv,
  u8 *ad,
  u32 adlen,
  u8 *plaintext,
  u32 len,
  u8 *cipher,
  u8 *tag
)
{
  bool ite;
  if (EverCrypt_AutoConfig2_wants_vale())
  {
    ite = EverCrypt_AutoConfig2_has_aesni();
  }
  else
  {
    ite = false;
  }
  if (ite)
  {
    u8 expanded[240U] = { 0U };
    old_aes256_key_expansion(key, expanded);
    {
      u8 iv_[16U] = { 0U };
      KRML_CHECK_SIZE(sizeof (u8), (len + (u32)15U) / (u32)16U * (u32)16U);
      {
        u8 plaintext_[(len + (u32)15U) / (u32)16U * (u32)16U];
        memset(plaintext_, 0U, (len + (u32)15U) / (u32)16U * (u32)16U * sizeof plaintext_[0U]);
        KRML_CHECK_SIZE(sizeof (u8), (len + (u32)15U) / (u32)16U * (u32)16U);
        {
          u8 cipher_[(len + (u32)15U) / (u32)16U * (u32)16U];
          memset(cipher_, 0U, (len + (u32)15U) / (u32)16U * (u32)16U * sizeof cipher_[0U]);
          KRML_CHECK_SIZE(sizeof (u8), (adlen + (u32)15U) / (u32)16U * (u32)16U);
          {
            u8 ad_[(adlen + (u32)15U) / (u32)16U * (u32)16U];
            memset(ad_, 0U, (adlen + (u32)15U) / (u32)16U * (u32)16U * sizeof ad_[0U]);
            memcpy(iv_, iv, (u32)12U * sizeof iv[0U]);
            memcpy(cipher_, cipher, len * sizeof cipher[0U]);
            memcpy(ad_, ad, adlen * sizeof ad[0U]);
            {
              gcm_args
              b =
                {
                  .plain = cipher_, .plain_len = (u64)len, .aad = ad_, .aad_len = (u64)adlen,
                  .iv = iv_, .expanded_key = expanded, .cipher = plaintext_, .tag = tag
                };
              u32 ret = old_gcm256_decrypt(&b);
              memcpy(plaintext, plaintext_, len * sizeof plaintext_[0U]);
              if (ret == (u32)0U)
              {
                return (u32)1U;
              }
              else
              {
                return (u32)0U;
              }
            }
          }
        }
      }
    }
  }
  else if (EverCrypt_AutoConfig2_wants_openssl())
  {
    return EverCrypt_OpenSSL_aes256_gcm_decrypt(key, iv, ad, adlen, plaintext, len, cipher, tag);
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "ERROR: inconsistent configuration (aes256_gcm_decrypt)");
    KRML_HOST_EXIT(255U);
  }
}

bool EverCrypt_uu___is_AES128_CBC(EverCrypt_block_cipher_alg projectee)
{
  switch (projectee)
  {
    case EverCrypt_AES128_CBC:
      {
        return true;
      }
    default:
      {
        return false;
      }
  }
}

bool EverCrypt_uu___is_AES256_CBC(EverCrypt_block_cipher_alg projectee)
{
  switch (projectee)
  {
    case EverCrypt_AES256_CBC:
      {
        return true;
      }
    default:
      {
        return false;
      }
  }
}

bool EverCrypt_uu___is_TDES_EDE_CBC(EverCrypt_block_cipher_alg projectee)
{
  switch (projectee)
  {
    case EverCrypt_TDES_EDE_CBC:
      {
        return true;
      }
    default:
      {
        return false;
      }
  }
}

u32 EverCrypt_block_cipher_keyLen(EverCrypt_block_cipher_alg uu___0_9512)
{
  switch (uu___0_9512)
  {
    case EverCrypt_AES128_CBC:
      {
        return (u32)16U;
      }
    case EverCrypt_AES256_CBC:
      {
        return (u32)32U;
      }
    case EverCrypt_TDES_EDE_CBC:
      {
        return (u32)24U;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

u32 EverCrypt_block_cipher_blockLen(EverCrypt_block_cipher_alg uu___1_9522)
{
  switch (uu___1_9522)
  {
    case EverCrypt_AES128_CBC:
      {
        return (u32)16U;
      }
    case EverCrypt_AES256_CBC:
      {
        return (u32)16U;
      }
    case EverCrypt_TDES_EDE_CBC:
      {
        return (u32)8U;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

bool EverCrypt_uu___is_RC4_128(EverCrypt_stream_cipher_alg projectee)
{
  return true;
}

bool EverCrypt_uu___is_AES128_GCM(EverCrypt_aead_alg projectee)
{
  switch (projectee)
  {
    case EverCrypt_AES128_GCM:
      {
        return true;
      }
    default:
      {
        return false;
      }
  }
}

bool EverCrypt_uu___is_AES256_GCM(EverCrypt_aead_alg projectee)
{
  switch (projectee)
  {
    case EverCrypt_AES256_GCM:
      {
        return true;
      }
    default:
      {
        return false;
      }
  }
}

bool EverCrypt_uu___is_CHACHA20_POLY1305(EverCrypt_aead_alg projectee)
{
  switch (projectee)
  {
    case EverCrypt_CHACHA20_POLY1305:
      {
        return true;
      }
    default:
      {
        return false;
      }
  }
}

bool EverCrypt_uu___is_AES128_CCM(EverCrypt_aead_alg projectee)
{
  switch (projectee)
  {
    case EverCrypt_AES128_CCM:
      {
        return true;
      }
    default:
      {
        return false;
      }
  }
}

bool EverCrypt_uu___is_AES256_CCM(EverCrypt_aead_alg projectee)
{
  switch (projectee)
  {
    case EverCrypt_AES256_CCM:
      {
        return true;
      }
    default:
      {
        return false;
      }
  }
}

bool EverCrypt_uu___is_AES128_CCM8(EverCrypt_aead_alg projectee)
{
  switch (projectee)
  {
    case EverCrypt_AES128_CCM8:
      {
        return true;
      }
    default:
      {
        return false;
      }
  }
}

bool EverCrypt_uu___is_AES256_CCM8(EverCrypt_aead_alg projectee)
{
  switch (projectee)
  {
    case EverCrypt_AES256_CCM8:
      {
        return true;
      }
    default:
      {
        return false;
      }
  }
}

KRML_DEPRECATED("Please use EverCrypt_AEAD.h (from C) or EverCrypt.AEAD.fsti (from F*) ")

u32 EverCrypt_aead_keyLen(EverCrypt_aead_alg uu___2_9629)
{
  switch (uu___2_9629)
  {
    case EverCrypt_AES128_GCM:
      {
        return (u32)16U;
      }
    case EverCrypt_AES256_GCM:
      {
        return (u32)32U;
      }
    case EverCrypt_CHACHA20_POLY1305:
      {
        return (u32)32U;
      }
    case EverCrypt_AES128_CCM:
      {
        return (u32)16U;
      }
    case EverCrypt_AES128_CCM8:
      {
        return (u32)16U;
      }
    case EverCrypt_AES256_CCM:
      {
        return (u32)32U;
      }
    case EverCrypt_AES256_CCM8:
      {
        return (u32)32U;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

KRML_DEPRECATED("Please use EverCrypt_AEAD.h (from C) or EverCrypt.AEAD.fsti (from F*) ")

u32 EverCrypt_aead_tagLen(EverCrypt_aead_alg uu___3_9643)
{
  switch (uu___3_9643)
  {
    case EverCrypt_AES128_CCM8:
      {
        return (u32)8U;
      }
    case EverCrypt_AES256_CCM8:
      {
        return (u32)8U;
      }
    case EverCrypt_AES128_GCM:
      {
        return (u32)16U;
      }
    case EverCrypt_AES256_GCM:
      {
        return (u32)16U;
      }
    case EverCrypt_CHACHA20_POLY1305:
      {
        return (u32)16U;
      }
    case EverCrypt_AES128_CCM:
      {
        return (u32)16U;
      }
    case EverCrypt_AES256_CCM:
      {
        return (u32)16U;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

KRML_DEPRECATED("Please use EverCrypt_AEAD.h (from C) or EverCrypt.AEAD.fsti (from F*) ")

u32 EverCrypt_aead_ivLen(EverCrypt_aead_alg a)
{
  return (u32)12U;
}

typedef struct EverCrypt__aead_state_s
{
  EverCrypt__aead_state_tags tag;
  union {
    FStar_Dyn_dyn case_AEAD_OPENSSL;
    FStar_Dyn_dyn case_AEAD_BCRYPT;
    u8 *case_AEAD_AES128_GCM_VALE;
    u8 *case_AEAD_AES256_GCM_VALE;
    u8 *case_AEAD_CHACHA20_POLY1305_HACL;
  }
  ;
}
EverCrypt__aead_state;

static bool EverCrypt_uu___is_AEAD_OPENSSL(EverCrypt__aead_state projectee)
{
  if (projectee.tag == EverCrypt_AEAD_OPENSSL)
  {
    return true;
  }
  else
  {
    return false;
  }
}

static bool EverCrypt_uu___is_AEAD_AES128_GCM_VALE(EverCrypt__aead_state projectee)
{
  if (projectee.tag == EverCrypt_AEAD_AES128_GCM_VALE)
  {
    return true;
  }
  else
  {
    return false;
  }
}

static bool EverCrypt_uu___is_AEAD_AES256_GCM_VALE(EverCrypt__aead_state projectee)
{
  if (projectee.tag == EverCrypt_AEAD_AES256_GCM_VALE)
  {
    return true;
  }
  else
  {
    return false;
  }
}

static bool EverCrypt_uu___is_AEAD_CHACHA20_POLY1305_HACL(EverCrypt__aead_state projectee)
{
  if (projectee.tag == EverCrypt_AEAD_CHACHA20_POLY1305_HACL)
  {
    return true;
  }
  else
  {
    return false;
  }
}

typedef EverCrypt__aead_state EverCrypt_aead_state_s;

KRML_DEPRECATED("Please use EverCrypt_AEAD.h (from C) or EverCrypt.AEAD.fsti (from F*) ")

EverCrypt__aead_state *EverCrypt_aead_create(EverCrypt_aead_alg alg, u8 *k1)
{
  EverCrypt__aead_state st;
  switch (alg)
  {
    case EverCrypt_AES128_GCM:
      {
        bool ite;
        if (EverCrypt_AutoConfig2_wants_vale())
        {
          ite = EverCrypt_AutoConfig2_has_aesni();
        }
        else
        {
          ite = false;
        }
        if (ite)
        {
          u8 *xk = KRML_HOST_CALLOC((u32)176U, sizeof (u8));
          old_aes128_key_expansion(k1, xk);
          st =
            (
              (EverCrypt__aead_state){
                .tag = EverCrypt_AEAD_AES128_GCM_VALE,
                { .case_AEAD_AES128_GCM_VALE = xk }
              }
            );
        }
        else if (EverCrypt_AutoConfig2_wants_openssl())
        {
          st =
            (
              (EverCrypt__aead_state){
                .tag = EverCrypt_AEAD_OPENSSL,
                {
                  .case_AEAD_OPENSSL = EverCrypt_OpenSSL_aead_create(EverCrypt_OpenSSL_AES128_GCM,
                    k1)
                }
              }
            );
        }
        else
        {
          st =
            KRML_EABORT(EverCrypt__aead_state,
              "ERROR: inconsistent configuration (aead_create/AES128_GCM)");
        }
        break;
      }
    case EverCrypt_AES256_GCM:
      {
        bool ite;
        if (EverCrypt_AutoConfig2_wants_vale())
        {
          ite = EverCrypt_AutoConfig2_has_aesni();
        }
        else
        {
          ite = false;
        }
        if (ite)
        {
          u8 *xk = KRML_HOST_CALLOC((u32)240U, sizeof (u8));
          old_aes256_key_expansion(k1, xk);
          st =
            (
              (EverCrypt__aead_state){
                .tag = EverCrypt_AEAD_AES256_GCM_VALE,
                { .case_AEAD_AES256_GCM_VALE = xk }
              }
            );
        }
        else if (EverCrypt_AutoConfig2_wants_openssl())
        {
          st =
            (
              (EverCrypt__aead_state){
                .tag = EverCrypt_AEAD_OPENSSL,
                {
                  .case_AEAD_OPENSSL = EverCrypt_OpenSSL_aead_create(EverCrypt_OpenSSL_AES256_GCM,
                    k1)
                }
              }
            );
        }
        else
        {
          st =
            KRML_EABORT(EverCrypt__aead_state,
              "ERROR: inconsistent configuration (aead_create/AES256_GCM)");
        }
        break;
      }
    case EverCrypt_CHACHA20_POLY1305:
      {
        if (EverCrypt_AutoConfig2_wants_hacl())
        {
          u8 *k01 = KRML_HOST_CALLOC((u32)32U, sizeof (u8));
          memcpy(k01, k1, (u32)32U * sizeof k1[0U]);
          st =
            (
              (EverCrypt__aead_state){
                .tag = EverCrypt_AEAD_CHACHA20_POLY1305_HACL,
                { .case_AEAD_CHACHA20_POLY1305_HACL = k01 }
              }
            );
        }
        else if (EverCrypt_AutoConfig2_wants_openssl())
        {
          st =
            (
              (EverCrypt__aead_state){
                .tag = EverCrypt_AEAD_OPENSSL,
                {
                  .case_AEAD_OPENSSL = EverCrypt_OpenSSL_aead_create(EverCrypt_OpenSSL_CHACHA20_POLY1305,
                    k1)
                }
              }
            );
        }
        else
        {
          st =
            KRML_EABORT(EverCrypt__aead_state,
              "ERROR: inconsistent configuration (aead_create/CHACHA20_POLY1305)");
        }
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  KRML_CHECK_SIZE(sizeof (EverCrypt__aead_state), (u32)1U);
  {
    EverCrypt__aead_state *buf = KRML_HOST_MALLOC(sizeof (EverCrypt__aead_state));
    buf[0U] = st;
    return buf;
  }
}

KRML_DEPRECATED("Please use EverCrypt_AEAD.h (from C) or EverCrypt.AEAD.fsti (from F*) ")

void
EverCrypt_aead_encrypt(
  EverCrypt__aead_state *pkey,
  u8 *iv,
  u8 *ad,
  u32 adlen,
  u8 *plaintext,
  u32 len,
  u8 *cipher,
  u8 *tag
)
{
  EverCrypt__aead_state k1 = *pkey;
  if (true && EverCrypt_uu___is_AEAD_AES128_GCM_VALE(k1))
  {
    u8 *xk;
    if (k1.tag == EverCrypt_AEAD_AES128_GCM_VALE)
    {
      xk = k1.case_AEAD_AES128_GCM_VALE;
    }
    else
    {
      xk = KRML_EABORT(u8 *, "unreachable (pattern matches are exhaustive in F*)");
    }
    {
      u8 iv_[16U] = { 0U };
      KRML_CHECK_SIZE(sizeof (u8), (len + (u32)15U) / (u32)16U * (u32)16U);
      {
        u8 plaintext_[(len + (u32)15U) / (u32)16U * (u32)16U];
        memset(plaintext_, 0U, (len + (u32)15U) / (u32)16U * (u32)16U * sizeof plaintext_[0U]);
        KRML_CHECK_SIZE(sizeof (u8), (len + (u32)15U) / (u32)16U * (u32)16U);
        {
          u8 cipher_[(len + (u32)15U) / (u32)16U * (u32)16U];
          memset(cipher_, 0U, (len + (u32)15U) / (u32)16U * (u32)16U * sizeof cipher_[0U]);
          KRML_CHECK_SIZE(sizeof (u8), (adlen + (u32)15U) / (u32)16U * (u32)16U);
          {
            u8 ad_[(adlen + (u32)15U) / (u32)16U * (u32)16U];
            memset(ad_, 0U, (adlen + (u32)15U) / (u32)16U * (u32)16U * sizeof ad_[0U]);
            memcpy(iv_, iv, (u32)12U * sizeof iv[0U]);
            memcpy(plaintext_, plaintext, len * sizeof plaintext[0U]);
            memcpy(ad_, ad, adlen * sizeof ad[0U]);
            {
              gcm_args
              b =
                {
                  .plain = plaintext_, .plain_len = (u64)len, .aad = ad_, .aad_len = (u64)adlen,
                  .iv = iv_, .expanded_key = xk, .cipher = cipher_, .tag = tag
                };
              old_gcm128_encrypt(&b);
              memcpy(cipher, cipher_, len * sizeof cipher_[0U]);
            }
          }
        }
      }
    }
  }
  else if (true && EverCrypt_uu___is_AEAD_AES256_GCM_VALE(k1))
  {
    u8 *xk;
    if (k1.tag == EverCrypt_AEAD_AES256_GCM_VALE)
    {
      xk = k1.case_AEAD_AES256_GCM_VALE;
    }
    else
    {
      xk = KRML_EABORT(u8 *, "unreachable (pattern matches are exhaustive in F*)");
    }
    {
      u8 iv_[16U] = { 0U };
      KRML_CHECK_SIZE(sizeof (u8), (len + (u32)15U) / (u32)16U * (u32)16U);
      {
        u8 plaintext_[(len + (u32)15U) / (u32)16U * (u32)16U];
        memset(plaintext_, 0U, (len + (u32)15U) / (u32)16U * (u32)16U * sizeof plaintext_[0U]);
        KRML_CHECK_SIZE(sizeof (u8), (len + (u32)15U) / (u32)16U * (u32)16U);
        {
          u8 cipher_[(len + (u32)15U) / (u32)16U * (u32)16U];
          memset(cipher_, 0U, (len + (u32)15U) / (u32)16U * (u32)16U * sizeof cipher_[0U]);
          KRML_CHECK_SIZE(sizeof (u8), (adlen + (u32)15U) / (u32)16U * (u32)16U);
          {
            u8 ad_[(adlen + (u32)15U) / (u32)16U * (u32)16U];
            memset(ad_, 0U, (adlen + (u32)15U) / (u32)16U * (u32)16U * sizeof ad_[0U]);
            memcpy(iv_, iv, (u32)12U * sizeof iv[0U]);
            memcpy(plaintext_, plaintext, len * sizeof plaintext[0U]);
            memcpy(ad_, ad, adlen * sizeof ad[0U]);
            {
              gcm_args
              b =
                {
                  .plain = plaintext_, .plain_len = (u64)len, .aad = ad_, .aad_len = (u64)adlen,
                  .iv = iv_, .expanded_key = xk, .cipher = cipher_, .tag = tag
                };
              old_gcm256_encrypt(&b);
              memcpy(cipher, cipher_, len * sizeof cipher_[0U]);
            }
          }
        }
      }
    }
  }
  else if (true && EverCrypt_uu___is_AEAD_CHACHA20_POLY1305_HACL(k1))
  {
    u8 *key;
    if (k1.tag == EverCrypt_AEAD_CHACHA20_POLY1305_HACL)
    {
      key = k1.case_AEAD_CHACHA20_POLY1305_HACL;
    }
    else
    {
      key = KRML_EABORT(u8 *, "unreachable (pattern matches are exhaustive in F*)");
    }
    Hacl_Chacha20Poly1305_32_aead_encrypt(key, iv, adlen, ad, len, plaintext, cipher, tag);
  }
  else if (true && EverCrypt_uu___is_AEAD_OPENSSL(k1))
  {
    FStar_Dyn_dyn key;
    if (k1.tag == EverCrypt_AEAD_OPENSSL)
    {
      key = k1.case_AEAD_OPENSSL;
    }
    else
    {
      key = KRML_EABORT(FStar_Dyn_dyn, "unreachable (pattern matches are exhaustive in F*)");
    }
    EverCrypt_OpenSSL_aead_encrypt(key, iv, ad, adlen, plaintext, len, cipher, tag);
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "ERROR: inconsistent configuration (aead_encrypt)");
    KRML_HOST_EXIT(255U);
  }
}

KRML_DEPRECATED("Please use EverCrypt_AEAD.h (from C) or EverCrypt.AEAD.fsti (from F*) ")

u32
EverCrypt_aead_decrypt(
  EverCrypt__aead_state *pkey,
  u8 *iv,
  u8 *ad,
  u32 adlen,
  u8 *plaintext,
  u32 len,
  u8 *cipher,
  u8 *tag
)
{
  EverCrypt__aead_state k1 = *pkey;
  if (true && EverCrypt_uu___is_AEAD_AES128_GCM_VALE(k1))
  {
    u8 *xk;
    if (k1.tag == EverCrypt_AEAD_AES128_GCM_VALE)
    {
      xk = k1.case_AEAD_AES128_GCM_VALE;
    }
    else
    {
      xk = KRML_EABORT(u8 *, "unreachable (pattern matches are exhaustive in F*)");
    }
    {
      u8 iv_[16U] = { 0U };
      KRML_CHECK_SIZE(sizeof (u8), (len + (u32)15U) / (u32)16U * (u32)16U);
      {
        u8 plaintext_[(len + (u32)15U) / (u32)16U * (u32)16U];
        memset(plaintext_, 0U, (len + (u32)15U) / (u32)16U * (u32)16U * sizeof plaintext_[0U]);
        KRML_CHECK_SIZE(sizeof (u8), (len + (u32)15U) / (u32)16U * (u32)16U);
        {
          u8 cipher_[(len + (u32)15U) / (u32)16U * (u32)16U];
          memset(cipher_, 0U, (len + (u32)15U) / (u32)16U * (u32)16U * sizeof cipher_[0U]);
          KRML_CHECK_SIZE(sizeof (u8), (adlen + (u32)15U) / (u32)16U * (u32)16U);
          {
            u8 ad_[(adlen + (u32)15U) / (u32)16U * (u32)16U];
            memset(ad_, 0U, (adlen + (u32)15U) / (u32)16U * (u32)16U * sizeof ad_[0U]);
            memcpy(iv_, iv, (u32)12U * sizeof iv[0U]);
            memcpy(cipher_, cipher, len * sizeof cipher[0U]);
            memcpy(ad_, ad, adlen * sizeof ad[0U]);
            {
              gcm_args
              b =
                {
                  .plain = cipher_, .plain_len = (u64)len, .aad = ad_, .aad_len = (u64)adlen,
                  .iv = iv_, .expanded_key = xk, .cipher = plaintext_, .tag = tag
                };
              u32 ret = old_gcm128_decrypt(&b);
              memcpy(plaintext, plaintext_, len * sizeof plaintext_[0U]);
              if (ret == (u32)0U)
              {
                return (u32)1U;
              }
              else
              {
                return (u32)0U;
              }
            }
          }
        }
      }
    }
  }
  else if (true && EverCrypt_uu___is_AEAD_AES256_GCM_VALE(k1))
  {
    u8 *xk;
    if (k1.tag == EverCrypt_AEAD_AES256_GCM_VALE)
    {
      xk = k1.case_AEAD_AES256_GCM_VALE;
    }
    else
    {
      xk = KRML_EABORT(u8 *, "unreachable (pattern matches are exhaustive in F*)");
    }
    {
      u8 iv_[16U] = { 0U };
      KRML_CHECK_SIZE(sizeof (u8), (len + (u32)15U) / (u32)16U * (u32)16U);
      {
        u8 plaintext_[(len + (u32)15U) / (u32)16U * (u32)16U];
        memset(plaintext_, 0U, (len + (u32)15U) / (u32)16U * (u32)16U * sizeof plaintext_[0U]);
        KRML_CHECK_SIZE(sizeof (u8), (len + (u32)15U) / (u32)16U * (u32)16U);
        {
          u8 cipher_[(len + (u32)15U) / (u32)16U * (u32)16U];
          memset(cipher_, 0U, (len + (u32)15U) / (u32)16U * (u32)16U * sizeof cipher_[0U]);
          KRML_CHECK_SIZE(sizeof (u8), (adlen + (u32)15U) / (u32)16U * (u32)16U);
          {
            u8 ad_[(adlen + (u32)15U) / (u32)16U * (u32)16U];
            memset(ad_, 0U, (adlen + (u32)15U) / (u32)16U * (u32)16U * sizeof ad_[0U]);
            memcpy(iv_, iv, (u32)12U * sizeof iv[0U]);
            memcpy(cipher_, cipher, len * sizeof cipher[0U]);
            memcpy(ad_, ad, adlen * sizeof ad[0U]);
            {
              gcm_args
              b =
                {
                  .plain = cipher_, .plain_len = (u64)len, .aad = ad_, .aad_len = (u64)adlen,
                  .iv = iv_, .expanded_key = xk, .cipher = plaintext_, .tag = tag
                };
              u32 ret = old_gcm256_decrypt(&b);
              memcpy(plaintext, plaintext_, len * sizeof plaintext_[0U]);
              if (ret == (u32)0U)
              {
                return (u32)1U;
              }
              else
              {
                return (u32)0U;
              }
            }
          }
        }
      }
    }
  }
  else if (true && EverCrypt_uu___is_AEAD_CHACHA20_POLY1305_HACL(k1))
  {
    u8 *key;
    if (k1.tag == EverCrypt_AEAD_CHACHA20_POLY1305_HACL)
    {
      key = k1.case_AEAD_CHACHA20_POLY1305_HACL;
    }
    else
    {
      key = KRML_EABORT(u8 *, "unreachable (pattern matches are exhaustive in F*)");
    }
    {
      u32
      r = Hacl_Chacha20Poly1305_32_aead_decrypt(key, iv, adlen, ad, len, plaintext, cipher, tag);
      return (u32)1U - r;
    }
  }
  else if (true && EverCrypt_uu___is_AEAD_OPENSSL(k1))
  {
    FStar_Dyn_dyn key;
    if (k1.tag == EverCrypt_AEAD_OPENSSL)
    {
      key = k1.case_AEAD_OPENSSL;
    }
    else
    {
      key = KRML_EABORT(FStar_Dyn_dyn, "unreachable (pattern matches are exhaustive in F*)");
    }
    return EverCrypt_OpenSSL_aead_decrypt(key, iv, ad, adlen, plaintext, len, cipher, tag);
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "ERROR: inconsistent configuration (aead_decrypt)");
    KRML_HOST_EXIT(255U);
  }
}

KRML_DEPRECATED("Please use EverCrypt_AEAD.h (from C) or EverCrypt.AEAD.fsti (from F*) ")

void EverCrypt_aead_free(EverCrypt__aead_state *pk)
{
  EverCrypt__aead_state k1 = *pk;
  if (true && EverCrypt_uu___is_AEAD_AES128_GCM_VALE(k1))
  {
    if (k1.tag == EverCrypt_AEAD_AES128_GCM_VALE)
    {
      u8 *xk = k1.case_AEAD_AES128_GCM_VALE;
      KRML_HOST_FREE(xk);
    }
    else
    {
      KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "unreachable (pattern matches are exhaustive in F*)");
      KRML_HOST_EXIT(255U);
    }
  }
  else if (true && EverCrypt_uu___is_AEAD_AES256_GCM_VALE(k1))
  {
    if (k1.tag == EverCrypt_AEAD_AES256_GCM_VALE)
    {
      u8 *xk = k1.case_AEAD_AES256_GCM_VALE;
      KRML_HOST_FREE(xk);
    }
    else
    {
      KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "unreachable (pattern matches are exhaustive in F*)");
      KRML_HOST_EXIT(255U);
    }
  }
  else if (true && EverCrypt_uu___is_AEAD_CHACHA20_POLY1305_HACL(k1))
  {
    if (k1.tag == EverCrypt_AEAD_CHACHA20_POLY1305_HACL)
    {
      u8 *key = k1.case_AEAD_CHACHA20_POLY1305_HACL;
      KRML_HOST_FREE(key);
    }
    else
    {
      KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "unreachable (pattern matches are exhaustive in F*)");
      KRML_HOST_EXIT(255U);
    }
  }
  else if (true && EverCrypt_uu___is_AEAD_OPENSSL(k1))
  {
    FStar_Dyn_dyn ite;
    if (k1.tag == EverCrypt_AEAD_OPENSSL)
    {
      ite = k1.case_AEAD_OPENSSL;
    }
    else
    {
      ite = KRML_EABORT(FStar_Dyn_dyn, "unreachable (pattern matches are exhaustive in F*)");
    }
    EverCrypt_OpenSSL_aead_free(ite);
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "ERROR: inconsistent configuration (aead_free)");
    KRML_HOST_EXIT(255U);
  }
  KRML_HOST_FREE(pk);
}

typedef struct EverCrypt__dh_state_s
{
  EverCrypt__dh_state_tags tag;
  FStar_Dyn_dyn st;
}
EverCrypt__dh_state;

static bool EverCrypt_uu___is_DH_OPENSSL(EverCrypt__dh_state projectee)
{
  if (projectee.tag == EverCrypt_DH_OPENSSL)
  {
    return true;
  }
  else
  {
    return false;
  }
}

typedef EverCrypt__dh_state EverCrypt_dh_state_s;

EverCrypt__dh_state
*EverCrypt_dh_load_group(
  u8 *dh_p,
  u32 dh_p_len,
  u8 *dh_g,
  u32 dh_g_len,
  u8 *dh_q,
  u32 dh_q_len
)
{
  EverCrypt__dh_state st;
  if (EverCrypt_AutoConfig2_wants_openssl())
  {
    st =
      (
        (EverCrypt__dh_state){
          .tag = EverCrypt_DH_OPENSSL,
          .st = EverCrypt_OpenSSL_dh_load_group(dh_p, dh_p_len, dh_g, dh_g_len, dh_q, dh_q_len)
        }
      );
  }
  else
  {
    st = KRML_EABORT(EverCrypt__dh_state, "ERROR: inconsistent configuration (dh_load_group)");
  }
  KRML_CHECK_SIZE(sizeof (EverCrypt__dh_state), (u32)1U);
  {
    EverCrypt__dh_state *buf = KRML_HOST_MALLOC(sizeof (EverCrypt__dh_state));
    buf[0U] = st;
    return buf;
  }
}

void EverCrypt_dh_free_group(EverCrypt__dh_state *st)
{
  EverCrypt__dh_state s = *st;
  if (true && EverCrypt_uu___is_DH_OPENSSL(s))
  {
    FStar_Dyn_dyn ite;
    if (s.tag == EverCrypt_DH_OPENSSL)
    {
      ite = s.st;
    }
    else
    {
      ite = KRML_EABORT(FStar_Dyn_dyn, "unreachable (pattern matches are exhaustive in F*)");
    }
    EverCrypt_OpenSSL_dh_free_group(ite);
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "ERROR: inconsistent configuration (dh_free_group)");
    KRML_HOST_EXIT(255U);
  }
  KRML_HOST_FREE(st);
}

u32 EverCrypt_dh_keygen(EverCrypt__dh_state *st, u8 *public)
{
  EverCrypt__dh_state s = *st;
  if (true && EverCrypt_uu___is_DH_OPENSSL(s))
  {
    FStar_Dyn_dyn ite;
    if (s.tag == EverCrypt_DH_OPENSSL)
    {
      ite = s.st;
    }
    else
    {
      ite = KRML_EABORT(FStar_Dyn_dyn, "unreachable (pattern matches are exhaustive in F*)");
    }
    return EverCrypt_OpenSSL_dh_keygen(ite, public);
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "ERROR: inconsistent configuration (dh_keygen)");
    KRML_HOST_EXIT(255U);
  }
}

u32 EverCrypt_dh_compute(EverCrypt__dh_state *st, u8 *public, u32 public_len, u8 *out1)
{
  EverCrypt__dh_state s = *st;
  if (true && EverCrypt_uu___is_DH_OPENSSL(s))
  {
    FStar_Dyn_dyn ite;
    if (s.tag == EverCrypt_DH_OPENSSL)
    {
      ite = s.st;
    }
    else
    {
      ite = KRML_EABORT(FStar_Dyn_dyn, "unreachable (pattern matches are exhaustive in F*)");
    }
    return EverCrypt_OpenSSL_dh_compute(ite, public, public_len, out1);
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "ERROR: inconsistent configuration (dh_compute)");
    KRML_HOST_EXIT(255U);
  }
}

bool EverCrypt_uu___is_ECC_P256(EverCrypt_ec_curve projectee)
{
  switch (projectee)
  {
    case EverCrypt_ECC_P256:
      {
        return true;
      }
    default:
      {
        return false;
      }
  }
}

bool EverCrypt_uu___is_ECC_P384(EverCrypt_ec_curve projectee)
{
  switch (projectee)
  {
    case EverCrypt_ECC_P384:
      {
        return true;
      }
    default:
      {
        return false;
      }
  }
}

bool EverCrypt_uu___is_ECC_P521(EverCrypt_ec_curve projectee)
{
  switch (projectee)
  {
    case EverCrypt_ECC_P521:
      {
        return true;
      }
    default:
      {
        return false;
      }
  }
}

bool EverCrypt_uu___is_ECC_X25519(EverCrypt_ec_curve projectee)
{
  switch (projectee)
  {
    case EverCrypt_ECC_X25519:
      {
        return true;
      }
    default:
      {
        return false;
      }
  }
}

bool EverCrypt_uu___is_ECC_X448(EverCrypt_ec_curve projectee)
{
  switch (projectee)
  {
    case EverCrypt_ECC_X448:
      {
        return true;
      }
    default:
      {
        return false;
      }
  }
}

typedef struct EverCrypt__ecdh_state_s
{
  EverCrypt__ecdh_state_tags tag;
  FStar_Dyn_dyn st;
}
EverCrypt__ecdh_state;

static bool EverCrypt_uu___is_ECDH_OPENSSL(EverCrypt__ecdh_state projectee)
{
  if (projectee.tag == EverCrypt_ECDH_OPENSSL)
  {
    return true;
  }
  else
  {
    return false;
  }
}

typedef EverCrypt__ecdh_state EverCrypt_ecdh_state_s;

EverCrypt__ecdh_state *EverCrypt_ecdh_load_curve(EverCrypt_ec_curve g1)
{
  EverCrypt__ecdh_state st;
  if (EverCrypt_AutoConfig2_wants_openssl())
  {
    EverCrypt_OpenSSL_ec_curve g_;
    switch (g1)
    {
      case EverCrypt_ECC_P256:
        {
          g_ = EverCrypt_OpenSSL_ECC_P256;
          break;
        }
      case EverCrypt_ECC_P384:
        {
          g_ = EverCrypt_OpenSSL_ECC_P384;
          break;
        }
      case EverCrypt_ECC_P521:
        {
          g_ = EverCrypt_OpenSSL_ECC_P521;
          break;
        }
      case EverCrypt_ECC_X25519:
        {
          g_ = EverCrypt_OpenSSL_ECC_X25519;
          break;
        }
      case EverCrypt_ECC_X448:
        {
          g_ = EverCrypt_OpenSSL_ECC_X448;
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    st =
      (
        (EverCrypt__ecdh_state){
          .tag = EverCrypt_ECDH_OPENSSL,
          .st = EverCrypt_OpenSSL_ecdh_load_curve(g_)
        }
      );
  }
  else
  {
    st = KRML_EABORT(EverCrypt__ecdh_state, "ERROR: inconsistent configuration (ecdh_load_curve)");
  }
  KRML_CHECK_SIZE(sizeof (EverCrypt__ecdh_state), (u32)1U);
  {
    EverCrypt__ecdh_state *buf = KRML_HOST_MALLOC(sizeof (EverCrypt__ecdh_state));
    buf[0U] = st;
    return buf;
  }
}

void EverCrypt_ecdh_free_curve(EverCrypt__ecdh_state *st)
{
  EverCrypt__ecdh_state s = *st;
  if (true && EverCrypt_uu___is_ECDH_OPENSSL(s))
  {
    FStar_Dyn_dyn ite;
    if (s.tag == EverCrypt_ECDH_OPENSSL)
    {
      ite = s.st;
    }
    else
    {
      ite = KRML_EABORT(FStar_Dyn_dyn, "unreachable (pattern matches are exhaustive in F*)");
    }
    EverCrypt_OpenSSL_ecdh_free_curve(ite);
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "ERROR: inconsistent configuration (ecdh_free_curve)");
    KRML_HOST_EXIT(255U);
  }
  KRML_HOST_FREE(st);
}

void EverCrypt_ecdh_keygen(EverCrypt__ecdh_state *st, u8 *outx, u8 *outy)
{
  EverCrypt__ecdh_state s = *st;
  if (true && EverCrypt_uu___is_ECDH_OPENSSL(s))
  {
    FStar_Dyn_dyn ite;
    if (s.tag == EverCrypt_ECDH_OPENSSL)
    {
      ite = s.st;
    }
    else
    {
      ite = KRML_EABORT(FStar_Dyn_dyn, "unreachable (pattern matches are exhaustive in F*)");
    }
    EverCrypt_OpenSSL_ecdh_keygen(ite, outx, outy);
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "ERROR: inconsistent configuration (ecdh_keygen)");
    KRML_HOST_EXIT(255U);
  }
}

u32 EverCrypt_ecdh_compute(EverCrypt__ecdh_state *st, u8 *inx, u8 *iny, u8 *out1)
{
  EverCrypt__ecdh_state s = *st;
  if (true && EverCrypt_uu___is_ECDH_OPENSSL(s))
  {
    FStar_Dyn_dyn ite;
    if (s.tag == EverCrypt_ECDH_OPENSSL)
    {
      ite = s.st;
    }
    else
    {
      ite = KRML_EABORT(FStar_Dyn_dyn, "unreachable (pattern matches are exhaustive in F*)");
    }
    return EverCrypt_OpenSSL_ecdh_compute(ite, inx, iny, out1);
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "ERROR: inconsistent configuration (ecdh_compute)");
    KRML_HOST_EXIT(255U);
  }
}
