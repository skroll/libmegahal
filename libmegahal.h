#ifndef LIBMEGAHAL_H
#define LIBMEGAHAL_H

#include <stdlib.h>

typedef struct megahal_ctx * megahal_ctx_t;
typedef struct megahal_model * megahal_model_t;
typedef struct megahal_personality * megahal_personality_t;
typedef struct megahal_dict * megahal_dict_t;
typedef struct megahal_swaplist * megahal_swaplist_t;

typedef void * (* megahal_alloc_func_t)(void *ctx, size_t sz);
typedef void * (* megahal_realloc_func_t)(void *ctx, void *ptr, size_t sz);
typedef void (* megahal_free_func_t)(void *ctx, void *ptr);

typedef struct {
	megahal_alloc_func_t    malloc;
	megahal_realloc_func_t  realloc;
	megahal_free_func_t     free;
	void                   *ctx;
} megahal_alloc_funcs_t;

int megahal_ctx_init(megahal_ctx_t *, megahal_alloc_funcs_t *);

int megahal_personality_init(megahal_ctx_t, megahal_personality_t *);

int megahal_personality_set_model(megahal_personality_t, megahal_model_t);
int megahal_personality_set_ban(megahal_personality_t, megahal_dict_t);
int megahal_personality_set_aux(megahal_personality_t, megahal_dict_t);
int megahal_personality_set_swap(megahal_personality_t, megahal_swaplist_t);

int megahal_model_init(megahal_ctx_t, megahal_model_t *);
int megahal_model_load_file(megahal_ctx_t, const char *, megahal_model_t *);
int megahal_model_save_file(megahal_model_t, const char *);

int megahal_dict_init(megahal_ctx_t, megahal_dict_t *);
int megahal_dict_add_word(megahal_dict_t, const char *);

int megahal_swaplist_init(megahal_ctx_t, megahal_swaplist_t *);
int megahal_swaplist_add_swap(megahal_swaplist_t, const char *, const char *);

int megahal_learn(megahal_personality_t, const char *);
int megahal_reply(megahal_personality_t pers, const char *str, char *outstr, size_t outlen);

#endif // LIBMEGAHAL_H

