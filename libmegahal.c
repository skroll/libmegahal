/*
 *  Copyright (C) 2014 Scott Kroll
 *  Original Copyright (C) 1998 Jason Hutchens
 *
 *  This program is free software; you can redistribute it and/or modify it
 *  under the terms of the GNU General Public License as published by the Free
 *  Softwae Foundation; either version 2 of the license or (at your option)
 *  any later version.
 *
 *  This program is distributed in the hope that it will be useful, but
 *  WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 *  or FITNESS FOR A PARTICULAR PURPOSE.  See the Gnu Public License for more
 *  details.
 *
 *  You should have received a copy of the GNU General Public License along
 *  with this program; if not, write to the Free Software Foundation, Inc.,
 *  675 Mass Ave, Cambridge, MA 02139, USA.
 */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <ctype.h>
#include <time.h>
#include <math.h>

#define TIMEOUT 1
#define COOKIE "MegaHALv8"

#define MIN(a,b) ((a)<(b))?(a):(b)

typedef struct {
	uint8_t length;
	char *word;
} STRING;

typedef struct {
	uint32_t size;
	STRING *entry;
	uint16_t *index;
} DICTIONARY;

typedef struct {
	uint16_t size;
	STRING *from;
	STRING *to;
} SWAP;

typedef struct NODE {
	uint16_t symbol;
	uint32_t usage;
	uint16_t count;
	uint16_t branch;
	struct NODE **tree;
} TREE;

typedef struct {
	uint8_t order;
	TREE *forward;
	TREE *backward;
	TREE **context;
	DICTIONARY *dictionary;
} MODEL;

static void train(MODEL *model, char *filename);
static void capitalize(char *string);
static bool word_exists(DICTIONARY *dictionary, STRING word);
static int babble(MODEL *model, DICTIONARY *keys, DICTIONARY *words);
static int rnd(int range);
static void upper(char *);
static int seed(MODEL *model, DICTIONARY *keys);
static bool boundary(char *string, int position);
static bool dissimilar(DICTIONARY *words1, DICTIONARY *words2);
static char * make_output(DICTIONARY *words);

static void change_personality(DICTIONARY *, unsigned int, MODEL **);
static void load_personality(MODEL **model);

static void initialize_context(MODEL *model);
static void update_context(MODEL *model, int symbol);
static MODEL * new_model(int order);
static void update_model(MODEL *model, int symbol);

static void learn(MODEL *, DICTIONARY *);

static bool load_model(char *filename, MODEL *model);
static void free_model(MODEL *model);
static void save_model(char *modelname, MODEL *model);

static void save_word(FILE *file, STRING word);
static void load_word(FILE *file, DICTIONARY *dictionary);
static uint16_t add_word(DICTIONARY *dictionary, STRING word);
static void make_words(char *input, DICTIONARY *words);
static uint16_t find_word(DICTIONARY *, STRING);
static void free_word(STRING word);
static void free_words(DICTIONARY *words);

static DICTIONARY * make_keywords(MODEL *model, DICTIONARY *words);

static TREE * add_symbol(TREE *tree, uint16_t symbol);
static TREE * find_symbol(TREE *node, int symbol);
static TREE * find_symbol_add(TREE *node, int symbol);
static void add_node(TREE *tree, TREE *node, int position);

static DICTIONARY *new_dictionary(void);
static void initialize_dictionary(DICTIONARY *);
static void load_dictionary(FILE *file, DICTIONARY *dictionary);
static int search_dictionary(DICTIONARY *dictionary, STRING word, bool *find);
static void free_dictionary(DICTIONARY *);
static void save_dictionary(FILE *file, DICTIONARY *dictionary);

static SWAP * new_swap(void);
static SWAP * initialize_swap(char *);
static void add_swap(SWAP *list, char *s, char *d);
static void free_swap(SWAP *swap);

static DICTIONARY * initialize_list(char *);

static void load_tree(FILE *file, TREE *node);
static void free_tree(TREE *);
static void save_tree(FILE *file, TREE *node);

static TREE * new_node(void);
static int search_node(TREE *node, int symbol, bool *found_symbol);

static int wordcmp(STRING word1, STRING word2);

static char * generate_reply(MODEL *model, DICTIONARY *words);
static DICTIONARY * reply(MODEL *model, DICTIONARY *keys);
static float evaluate_reply(MODEL *model, DICTIONARY *keys, DICTIONARY *words);

static void add_key(MODEL *model, DICTIONARY *keys, STRING word);
static void add_aux(MODEL *model, DICTIONARY *keys, STRING word);

static DICTIONARY *ban = NULL;
static DICTIONARY *words = NULL;
static DICTIONARY *aux = NULL;

static SWAP *swp = NULL;
static bool used_key;

static MODEL *model = NULL;

static int order = 5;
static char *directory = NULL;
static char *last = NULL;

#define SEP "/"
#define DEFAULT "."

void
megahal_initialize(void)
{
	words = new_dictionary();
	change_personality(NULL, 0, &model);
}

char *
megahal_do_reply(char *input)
{
	char *output = NULL;

	upper(input);

	make_words(input, words);

	learn(model, words);
	output = generate_reply(model, words);
	capitalize(output);

	return output;
}


void
megahal_learn_no_reply(char *input)
{
	upper(input);

	make_words(input, words);

	learn(model, words);
}

void megahal_cleanup(void)
{
	save_model("megahal.brn", model);
}

static DICTIONARY *
new_dictionary(void)
{
	DICTIONARY *dictionary = NULL;

	dictionary = (DICTIONARY *)malloc(sizeof(DICTIONARY));

	if (dictionary == NULL) {
		return NULL;
	}

	dictionary->size = 0;
	dictionary->index = NULL;
	dictionary->entry = NULL;

	return dictionary;
}

static void
change_personality(DICTIONARY *command, unsigned int position, MODEL **model)
{
	if (directory == NULL) {
		directory = (char *)malloc(sizeof(char) * (strlen(DEFAULT) + 1));
		if (directory == NULL) {
			// TODO: Error
			// error("change_personality", "Unable to allocate directory");
		} else {
			strcpy(directory, DEFAULT);
		}
	}

	if (last == NULL) {
		last = strdup(directory);
	}

	if ((command == NULL) || ((position + 2) >= command->size)) {
		/* no dir set, so we leave it to whatever was set above */
	} else {
		directory = (char *)realloc(directory, sizeof(char) * (command->entry[position + 2].length + 1));
		if (directory == NULL) {
			// TODO: Error
			// error("change_personality", "Unable to allocate directory");
		}
		strncpy(directory, command->entry[position + 2].word, command->entry[position + 2].length);
		directory[command->entry[position + 2].length] = '\0';
	}

	load_personality(model);
}

static void
load_personality(MODEL **model)
{
	FILE *file;
	static char *filename=NULL;

	if (filename == NULL) {
		filename = (char *)malloc(sizeof(char) * 1);
	}

	/* Allocate memory for the filename */
	filename = (char *)realloc(filename, sizeof(char) * (strlen(directory) + strlen(SEP) + 12));

	if (filename == NULL) {
		// TODO: Error
		// error("load_personality","Unable to allocate filename");
	}

	/* Check to see if the brain exists */
	if (strcmp(directory, last) != 0) {
		sprintf(filename, "%s%smegahal.brn", directory, SEP);
		file = fopen(filename, "r");

		if (file == NULL) {
			sprintf(filename, "%s%smegahal.trn", directory, SEP);
			file = fopen(filename, "r");

			if (file == NULL) {
				fprintf(stdout, "Unable to change MegaHAL personality to \"%s\".\n"
				                "Reverting to MegaHAL personality \"%s\".\n", directory, last);
				free(directory);
				directory = strdup(last);
				return;
			}
		}

		fclose(file);
		fprintf(stdout, "Changing to MegaHAL personality \"%s\".\n", directory);
	}

	/* Free the current personality */
	free_model(*model);
	free_words(ban);
	free_dictionary(ban);
	free_words(aux);
	free_dictionary(aux);
	free_swap(swp);

	/* Create a language model. */
	*model = new_model(order);

	/* Train the model on a text if one exists */
	sprintf(filename, "%s%smegahal.brn", directory, SEP);

	if (load_model(filename, *model) == false) {
		sprintf(filename, "%s%smegahal.trn", directory, SEP);
		train(*model, filename);
	}

	/* Read a dictionary containing banned keywords, auxiliary keywords,
	 * greeting keywords and swap keywords */
	sprintf(filename, "%s%smegahal.ban", directory, SEP);
	ban = initialize_list(filename);
	sprintf(filename, "%s%smegahal.aux", directory, SEP);
	aux = initialize_list(filename);
	sprintf(filename, "%s%smegahal.swp", directory, SEP);
	swp = initialize_swap(filename);
}

static MODEL *
new_model(int order)
{
	MODEL *model = NULL;

	model = (MODEL *)malloc(sizeof(MODEL));
	if (model==NULL) {
		// TODO: Error
		// error("new_model", "Unable to allocate model.");
		goto fail;
	}

	model->order = order;
	model->forward = new_node();
	model->backward = new_node();
	model->context = (TREE **)malloc(sizeof(TREE *) * (order + 2));

	if (model->context == NULL) {
		// TODO: Error
		// error("new_model", "Unable to allocate context array.");
		goto fail;
	}

	initialize_context(model);
	model->dictionary = new_dictionary();
	initialize_dictionary(model->dictionary);

	return model;

fail:
	return NULL;
}

static void
initialize_context(MODEL *model)
{
	register unsigned int i;

	for (i =0 ; i <= model->order; ++i) {
		model->context[i] = NULL;
	}
}

static void
update_context(MODEL *model, int symbol)
{
	register unsigned int i;

	for (i = (model->order + 1); i > 0; --i) {
		if (model->context[i - 1] != NULL) {
			model->context[i] = find_symbol(model->context[i - 1], symbol);
		}
	}
}

void
free_model(MODEL *model)
{
	if (model == NULL) {
		return;
	}

	if (model->forward != NULL) {
		free_tree(model->forward);
	}

	if (model->backward != NULL) {
		free_tree(model->backward);
	}

	if (model->context != NULL) {
		free(model->context);
	}

	if (model->dictionary != NULL) {
		free_dictionary(model->dictionary);
		free(model->dictionary);
	}

	free(model);
}

static void
learn(MODEL *model, DICTIONARY *words)
{
	register unsigned int i;
	register int j;
	uint16_t symbol;

	/* We only learn from inputs which are long enough */
	if (words->size <= (model->order)) {
		return;
	}

	/* Train the model in the forwards direction. Start by initializing the
	 * context of the model. */
	initialize_context(model);
	model->context[0] = model->forward;

	for (i = 0; i < words->size; ++i) {
		/* Add the symbol to the model's dictionary if necessary, and then
		 * update the forward model accordingly. */
		symbol = add_word(model->dictionary, words->entry[i]);
		update_model(model, symbol);
	}

	/* Add the sentence-terminating symbol. */
	update_model(model, 1);

	/* Train the model in the backwards direction.  Start by initializing
	 * the context of the model. */
	initialize_context(model);
	model->context[0] = model->backward;

	for (j = words->size - 1; j >= 0; --j) {
		/* Find the symbol in the model's dictionary, and then update the
		 * backward model accordingly. */
		symbol = find_word(model->dictionary, words->entry[j]);
		update_model(model, symbol);
	}

	/* Add the sentence-terminating symbol. */
	update_model(model, 1);

	return;
}

static bool
load_model(char *filename, MODEL *model)
{
	FILE *file;
	char cookie[16];

	if (filename == NULL) {
		return false;
	}

	file = fopen(filename, "rb");

	if (file == NULL) {
		// warn("load_model", "Unable to open file `%s'", filename);
		// TODO: warn
		return false;
	}

	fread(cookie, sizeof(char), strlen(COOKIE), file);

	if (strncmp(cookie, COOKIE, strlen(COOKIE)) != 0) {
		// TODO: warn
		//warn("load_model", "File `%s' is not a MegaHAL brain", filename);
		goto fail;
	}

	fread(&(model->order), sizeof(uint8_t), 1, file);
	load_tree(file, model->forward);
	load_tree(file, model->backward);
	load_dictionary(file, model->dictionary);

	return true;
fail:
	fclose(file);

	return false;
}

static void
update_model(MODEL *model, int symbol)
{
	register unsigned int i;

	/* Update all of the models in the current context with the specified
	 * symbol. */
	for (i = (model->order + 1); i > 0; --i) {
		if (model->context[i - 1] != NULL) {
			model->context[i] = add_symbol(model->context[i - 1], (uint16_t)symbol);
		}
	}

	return;
}

static uint16_t
add_word(DICTIONARY *dictionary, STRING word)
{
	register int i;
	int position;
	bool found;

	/* If the word's already in the dictionary, there is no need to add it */
	position = search_dictionary(dictionary, word, &found);
	if (found == true) {
		goto succeed;
	}

	/* Increase the number of words in the dictionary */
	dictionary->size += 1;

	/* Allocate one more entry for the word index */
	if (dictionary->index == NULL) {
		dictionary->index=(uint16_t *)malloc(sizeof(uint16_t) * (dictionary->size));
	} else {
		dictionary->index=(uint16_t *)realloc((uint16_t *)(dictionary->index), sizeof(uint16_t) * (dictionary->size));
	}

	if (dictionary->index == NULL) {
		// error("add_word", "Unable to reallocate the index.");
		// TODO: Error
		goto fail;
	}

	/* Allocate one more entry for the word array */
	if (dictionary->entry == NULL) {
		dictionary->entry = (STRING *)malloc(sizeof(STRING) * (dictionary->size));
	} else {
		dictionary->entry = (STRING *)realloc((STRING *)(dictionary->entry), sizeof(STRING) * (dictionary->size));
	}

	if (dictionary->entry == NULL) {
		// error("add_word", "Unable to reallocate the dictionary to %d elements.", dictionary->size);
		// TODO: Error
		goto fail;
	}

	/* Copy the new word into the word array */
	dictionary->entry[dictionary->size - 1].length = word.length;
	dictionary->entry[dictionary->size - 1].word = (char *)malloc(sizeof(char) * (word.length));
	if (dictionary->entry[dictionary->size - 1].word == NULL) {
		// error("add_word", "Unable to allocate the word.");
		goto fail;
	}

	for (i = 0; i < word.length; ++i) {
		dictionary->entry[dictionary->size - 1].word[i] = word.word[i];
	}

	/* Shuffle the word index to keep it sorted alphabetically */
	for (i = (dictionary->size - 1); i > position; --i) {
		dictionary->index[i] = dictionary->index[i-1];
	}

	/* Copy the new symbol identifier into the word index */
	dictionary->index[position]=dictionary->size-1;

succeed:
	return dictionary->index[position];

fail:
	return 0;
}

static void
save_word(FILE *file, STRING word)
{
	register unsigned int i;

	fwrite(&(word.length), sizeof(uint8_t), 1, file);

	for (i = 0; i < word.length; ++i) {
		fwrite(&(word.word[i]), sizeof(char), 1, file);
	}
}


static void
load_word(FILE *file, DICTIONARY *dictionary)
{
	register unsigned int i;
	STRING word;

	fread(&(word.length), sizeof(uint8_t), 1, file);
	word.word = (char *)malloc(sizeof(char) * word.length);

	if (word.word == NULL) {
		// TODO: Error
		// error("load_word", "Unable to allocate word");
		return;
	}

	for (i = 0; i < word.length; ++i) {
		fread(&(word.word[i]), sizeof(char), 1, file);
	}

	add_word(dictionary, word);
	free(word.word);
}

static void
make_words(char *input, DICTIONARY *words)
{
	int offset = 0;

	/* Clear the entries in the dictionary */
	free_dictionary(words);

	/* If the string is empty then do nothing, for it contains no words. */
	if (strlen(input) == 0) {
		return;
	}

	/* Loop forever. */
	while (1) {
		/* If the current character is of the same type as the previous
		 * character, then include it in the word.  Otherwise, terminate
		 * the current word. */
		if (boundary(input, offset)) {
			/* Add the word to the dictionary */
			if (words->entry == NULL) {
				words->entry = (STRING *)malloc((words->size + 1) * sizeof(STRING));
			} else {
				words->entry = (STRING *)realloc(words->entry, (words->size + 1) * sizeof(STRING));
			}

			if (words->entry == NULL) {
				// TODO: Error
				// error("make_words", "Unable to reallocate dictionary");
				return;
			}

			words->entry[words->size].length = offset;
			words->entry[words->size].word = input;
			words->size += 1;

			if (offset == (int)strlen(input)) {
				break;
			}

			input += offset;
			offset = 0;
		} else {
			++offset;
		}
	}

	/* If the last word isn't punctuation, then replace it with a full-stop
	 * character. */
	if (isalnum(words->entry[words->size-1].word[0])) {
		if (words->entry == NULL) {
			words->entry = (STRING *)malloc((words->size + 1) * sizeof(STRING));
		} else {
			words->entry = (STRING *)realloc(words->entry, (words->size + 1) * sizeof(STRING));
		}

		if (words->entry == NULL) {
			// error("make_words", "Unable to reallocate dictionary");
			// TODO: Error
			return;
		}

		words->entry[words->size].length = 1;
		words->entry[words->size].word = ".";
		++words->size;
	} else if(strchr("!.?", words->entry[words->size - 1].word[words->entry[words->size - 1].length - 1])==NULL) {
		words->entry[words->size - 1].length = 1;
		words->entry[words->size - 1].word = ".";
	}

	return;
}

static uint16_t
find_word(DICTIONARY *dictionary, STRING word)
{
	int position;
	bool found;

	position = search_dictionary(dictionary, word, &found);

	if (found == true) {
		return dictionary->index[position];
	} else {
		return 0;
	}
}

static void
free_word(STRING word)
{
	free(word.word);
}

static void
free_words(DICTIONARY *words)
{
	register unsigned int i;

	if (words == NULL) {
		return;
	}

	if (words->entry != NULL) {
		for (i = 0; i < words->size; ++i) {
			free_word(words->entry[i]);
		}
	}
}

static void
initialize_dictionary(DICTIONARY *dictionary)
{
	STRING word = { 7, "<ERROR>" };
	STRING end = { 5, "<FIN>" };

	(void)add_word(dictionary, word);
	(void)add_word(dictionary, end);
}

static void
load_dictionary(FILE *file, DICTIONARY *dictionary)
{
	register int i;
	int size;

	fread(&size, sizeof(uint32_t), 1, file);

	for (i = 0; i < size; ++i) {
		load_word(file, dictionary);
	}
}

static int
search_dictionary(DICTIONARY *dictionary, STRING word, bool *find)
{
	int position;
	int min;
	int max;
	int middle;
	int compar;

	/* If the dictionary is empty, then obviously the word won't be found */
	if (dictionary->size == 0) {
		position = 0;
		goto notfound;
	}

	/* Initialize the lower and upper bounds of the search */
	min = 0;
	max = dictionary->size - 1;

	/* Search repeatedly, halving the search space each time, until either
	 * the entry is found, or the search space becomes empty */
	while (1) {
		/* See whether the middle element of the search space is greater
		 * than, equal to, or less than the element being searched for. */
		middle = (min + max) / 2;
		compar = wordcmp(word, dictionary->entry[dictionary->index[middle]]);

		/* If it is equal then we have found the element.  Otherwise we
		 * can halve the search space accordingly. */
		if (compar == 0) {
			position = middle;
			goto found;
		} else if (compar > 0) {
			if (max == middle) {
				position = middle + 1;
				goto notfound;
			}
			min = middle + 1;
		} else {
			if (min == middle) {
				position = middle;
				goto notfound;
			}
			max = middle - 1;
		}
	}

found:
	*find = true;
	return position;

notfound:
	*find = false;
	return position;
}

static void
free_dictionary(DICTIONARY *dictionary)
{
	if (dictionary == NULL) {
		return;
	}

	if (dictionary->entry != NULL) {
		free(dictionary->entry);
		dictionary->entry = NULL;
	}

	if (dictionary->index != NULL) {
		free(dictionary->index);
		dictionary->index=NULL;
	}

	dictionary->size = 0;
}

static SWAP *
initialize_swap(char *filename)
{
	SWAP *list;
	FILE *file = NULL;
	char buffer[1024];
	char *from;
	char *to;

	list = new_swap();

	if (filename == NULL) {
		return list;
	}

	file = fopen(filename, "r");
	if (file == NULL) {
		return list;
	}

	while (!feof(file)) {
		if (fgets(buffer, 1024, file) == NULL) {
			break;
		}

		if (buffer[0] == '#') {
			continue;
		}

		from = strtok(buffer, "\t ");
		to = strtok(NULL, "\t \n#");

		add_swap(list, from, to);
	}

	fclose(file);
	return list;
}

static void
free_swap(SWAP *swap)
{
	register int i;

	if (swap==NULL) {
		return;
	}

	for (i = 0; i < swap->size; ++i) {
		free_word(swap->from[i]);
		free_word(swap->to[i]);
	}

	free(swap->from);
	free(swap->to);
	free(swap);
}

static DICTIONARY *
initialize_list(char *filename)
{
	DICTIONARY *list;
	FILE *file = NULL;
	STRING word;
	char *string;
	char buffer[1024];

	list = new_dictionary();

	if (filename == NULL) {
		return list;
	}

	file = fopen(filename, "r");
	if (file == NULL) {
		return list;
	}

	while (!feof(file)) {
		if (fgets(buffer, 1024, file) == NULL) {
			break;
		}

		if (buffer[0]== '#' ) {
			continue;
		}

		string = strtok(buffer, "\t \n#");

		if ((string != NULL) && (strlen(string) > 0)) {
			word.length = strlen(string);
			word.word = strdup(buffer);
			add_word(list, word);
		}
	}

	fclose(file);
	return list;
}

static TREE *
new_node(void)
{
	TREE *node = NULL;

	/* Allocate memory for the new node */
	node = (TREE *)malloc(sizeof(TREE));
	if (node == NULL) {
		// TODO: error
		//error("new_node", "Unable to allocate the node.");
		goto fail;
	}

	/* Initialise the contents of the node */
	node->symbol = 0;
	node->usage = 0;
	node->count = 0;
	node->branch = 0;
	node->tree = NULL;

	return node;

fail:
	if (node != NULL) {
		free(node);
	}

	return NULL;
}

static void
load_tree(FILE *file, TREE *node)
{
	static int level = 0;
	register unsigned int i;

	fread(&(node->symbol), sizeof(uint16_t), 1, file);
	fread(&(node->usage), sizeof(uint32_t), 1, file);
	fread(&(node->count), sizeof(uint16_t), 1, file);
	fread(&(node->branch), sizeof(uint16_t), 1, file);

	if (node->branch ==0 ) {
		return;
	}

	node->tree = (TREE **)malloc(sizeof(TREE *) * (node->branch));
	if (node->tree == NULL) {
		//error("load_tree", "Unable to allocate subtree");
		// TODO: Error
		return;
	}

	for (i = 0; i < node->branch; ++i) {
		node->tree[i]=new_node();
		++level;
		load_tree(file, node->tree[i]);
		--level;
	}
}

static void
free_tree(TREE *tree)
{
	static int level = 0;
	register unsigned int i;

	if (tree == NULL) {
		return;
	}

	if (tree->tree!=NULL) {
		for (i = 0; i < tree->branch; ++i) {
			++level;
			free_tree(tree->tree[i]);
			--level;
		}

		free(tree->tree);
	}

	free(tree);
}

static SWAP *
new_swap(void)
{
	SWAP *list;

	list = (SWAP *)malloc(sizeof(SWAP));

	if (list == NULL) {
		// error("new_swap", "Unable to allocate swap");
		// TODO: Error
		return NULL;
	}

	list->size = 0;
	list->from = NULL;
	list->to = NULL;

	return list;
}

static void
add_swap(SWAP *list, char *s, char *d)
{
	list->size += 1;

	if (list->from == NULL) {
		list->from = (STRING *)malloc(sizeof(STRING));

		if (list->from == NULL) {
			// error("add_swap", "Unable to allocate list->from");
			// TODO: Error
			return;
		}
	}

	if (list->to == NULL) {
		list->to = (STRING *)malloc(sizeof(STRING));
		if (list->to == NULL) {
			//error("add_swap", "Unable to allocate list->to");
			//TODO: Error
			return;
		}
	}

	list->from = (STRING *)realloc(list->from, sizeof(STRING) * (list->size));
	if (list->from == NULL) {
		//error("add_swap", "Unable to reallocate from");
		//TODO: Error
		return;
	}

	list->to = (STRING *)realloc(list->to, sizeof(STRING) * (list->size));
	if (list->to==NULL) {
		//error("add_swap", "Unable to reallocate to");
		//TODO: Error
		return;
	}

	list->from[list->size - 1].length = strlen(s);
	list->from[list->size - 1].word = strdup(s);
	list->to[list->size - 1].length = strlen(d);
	list->to[list->size - 1].word = strdup(d);
}

static int
wordcmp(STRING word1, STRING word2)
{
	register int i;
	int bound;

	bound = MIN(word1.length, word2.length);

	for (i = 0; i < bound; ++i) {
		if (toupper(word1.word[i]) != toupper(word2.word[i])) {
			return (int)(toupper(word1.word[i]) - toupper(word2.word[i]));
		}
	}

	if (word1.length < word2.length) {
		return -1;
	}

	if (word1.length > word2.length) {
		return 1;
	}

	return 0;
}

static void
upper(char *string)
{
	register unsigned int i;

	for (i = 0; i < strlen(string); ++i) {
		string[i] = (char)toupper((int)string[i]);
	}
}

static bool
boundary(char *string, int position)
{
	if (position == 0) {
		return false;
	}

	if (position == (int)strlen(string)) {
		return true;
	}

	if ((string[position] == '\'') &&
	    (isalpha(string[position - 1]) != 0) &&
	    (isalpha(string[position + 1]) != 0)) {
		return false;
	}

	if ((position > 1) &&
	    (string[position - 1]=='\'') &&
	    (isalpha(string[position - 2]) != 0) &&
	    (isalpha(string[position]) != 0)) {
		return false;
	}

	if ((isalpha(string[position]) !=0 ) &&
	    (isalpha(string[position - 1]) == 0)) {
		return true;
	}

	if ((isalpha(string[position]) == 0) &&
	    (isalpha(string[position - 1]) != 0)) {
		return true;
	}

	if (isdigit(string[position]) != isdigit(string[position - 1])) {
		return true;
	}

	return false;
}

static TREE *
add_symbol(TREE *tree, uint16_t symbol)
{
	TREE *node = NULL;

	/* Search for the symbol in the subtree of the tree node. */
	node = find_symbol_add(tree, symbol);

	/* Increment the symbol counts */
	if (node->count < 65535) {
		node->count += 1;
		tree->usage += 1;
	}

	return node;
}

static TREE *
find_symbol(TREE *node, int symbol)
{
	register unsigned int i;
	TREE *found = NULL;
	bool found_symbol = false;

	/* Perform a binary search for the symbol. */
	i = search_node(node, symbol, &found_symbol);
	if (found_symbol == true) {
		found = node->tree[i];
	}

	return found;
}

static TREE *
find_symbol_add(TREE *node, int symbol)
{
	register unsigned int i;
	TREE *found = NULL;
	bool found_symbol = false;

	/* Perform a binary search for the symbol.  If the symbol isn't found,
	 * attach a new sub-node to the tree node so that it remains sorted. */
	i = search_node(node, symbol, &found_symbol);

	if (found_symbol == true) {
		found=node->tree[i];
	} else {
		found=new_node();
		found->symbol = symbol;
		add_node(node, found, i);
	}

	return found;
}

static int
search_node(TREE *node, int symbol, bool *found_symbol)
{
	register unsigned int position;
	int min;
	int max;
	int middle;
	int compar;

	/* Handle the special case where the subtree is empty. */
	if (node->branch == 0) {
		position = 0;
		goto notfound;
	}

	/* Perform a binary search on the subtree. */
	min = 0;
	max = node->branch - 1;
	while (true) {
		middle = (min + max) / 2;
		compar = symbol-node->tree[middle]->symbol;
		if (compar == 0) {
			position = middle;
			goto found;
		} else if (compar > 0) {
			if (max == middle) {
				position = middle + 1;
				goto notfound;
			}
			min = middle + 1;
		} else {
			if (min == middle) {
				position = middle;
				goto notfound;
			}
			max = middle - 1;
		}
	}

found:
	*found_symbol = true;
	return position;

notfound:
	*found_symbol = false;
	return position;
}

static void
add_node(TREE *tree, TREE *node, int position)
{
	register int i;

	/* Allocate room for one more child node, which may mean allocating
	 * the sub-tree from scratch. */
	if (tree->tree == NULL) {
		tree->tree=(TREE **)malloc(sizeof(TREE *) * (tree->branch + 1));
	} else {
		tree->tree=(TREE **)realloc((TREE **)(tree->tree),sizeof(TREE *) * (tree->branch + 1));
	}

	if (tree->tree == NULL) {
		// error("add_node", "Unable to reallocate subtree.");
		// TODO: Error
		return;
	}

	/* Shuffle the nodes down so that we can insert the new node at the
	 * subtree index given by position. */
	for (i = tree->branch; i > position; --i) {
		tree->tree[i]=tree->tree[i - 1];
	}

	/* Add the new node to the sub-tree. */
	tree->tree[position] = node;
	tree->branch += 1;
}

static char *
generate_reply(MODEL *model, DICTIONARY *words)
{
	static DICTIONARY *dummy = NULL;
	DICTIONARY *replywords;
	DICTIONARY *keywords;
	float surprise;
	float max_surprise;
	char *output;
	static char *output_none = NULL;
	int count;
	int basetime;
	int timeout = TIMEOUT;

	/* Create an array of keywords from the words in the user's input */
	keywords = make_keywords(model, words);

	/* Make sure some sort of reply exists */
	if (output_none == NULL) {
		output_none = malloc(40);
		if (output_none != NULL) {
			strcpy(output_none, "I don't know enough to answer you yet!");
		}
	}

	output = output_none;

	if (dummy == NULL) {
		dummy = new_dictionary();
	}

	replywords = reply(model, dummy);

	if (dissimilar(words, replywords) == true) {
		output = make_output(replywords);
	}

	/* Loop for the specified waiting period, generating and evaluating
	 * replies */
	max_surprise = (float)-1.0;
	count = 0;
	basetime = time(NULL);
#if 0
	do {
		replywords = reply(model, keywords);
		surprise = evaluate_reply(model, keywords, replywords);
		++count;
		if ((surprise>max_surprise) && (dissimilar(words, replywords) == true)) {
			max_surprise = surprise;
			output = make_output(replywords);
		}
	} while ((time(NULL) - basetime) < timeout);
#else
	int i;
	for (i = 0; i < 9000; i++) {
		replywords = reply(model, keywords);
		surprise = evaluate_reply(model, keywords, replywords);
		++count;
		if ((surprise>max_surprise) && (dissimilar(words, replywords) == true)) {
			max_surprise = surprise;
			output = make_output(replywords);
		}
	}
#endif

	/* Return the best answer we generated */
	return output;
}

static DICTIONARY *
make_keywords(MODEL *model, DICTIONARY *words)
{
	static DICTIONARY *keys = NULL;
	register unsigned int i;
	register unsigned int j;
	int c;

	if (keys==NULL) {
		keys = new_dictionary();
	}

	for (i = 0; i < keys->size; ++i) {
		free(keys->entry[i].word);
	}

	free_dictionary(keys);

	for (i = 0; i < words->size; ++i) {
		/* Find the symbol ID of the word.  If it doesn't exist in the
		 * model, or if it begins with a non-alphanumeric character, or if
		 * it is in the exclusion array, then skip over it. */
		c = 0;
		for (j = 0; j < swp->size; ++j) {
			if (wordcmp(swp->from[j], words->entry[i]) == 0) {
				add_key(model, keys, swp->to[j]);
				++c;
			}
		}

		if (c == 0) {
			add_key(model, keys, words->entry[i]);
		}
	}

	if (keys->size > 0) {
		for (i = 0; i < words->size; ++i) {
			c =0;
			for (j = 0; j < swp->size; ++j) {
				if (wordcmp(swp->from[j], words->entry[i]) == 0) {
					add_aux(model, keys, swp->to[j]);
					++c;
				}
			}

			if (c == 0) {
				add_aux(model, keys, words->entry[i]);
			}
		}
	}

	return keys;
}

static bool
dissimilar(DICTIONARY *words1, DICTIONARY *words2)
{
	register unsigned int i;

	if (words1->size != words2->size) {
		return true;
	}

	for (i = 0; i < words1->size; ++i) {
		if (wordcmp(words1->entry[i], words2->entry[i]) != 0) {
			return true;
		}
	}

	return false;
}

static char *
make_output(DICTIONARY *words)
{
	static char *output = NULL;
	register unsigned int i;
	register int j;
	int length;
	static char *output_none = NULL;

	if (output_none == NULL) {
		output_none = malloc(40);
	}

	if (output == NULL) {
		output = (char *)malloc(sizeof(char));
		if (output == NULL) {
			//error("make_output", "Unable to allocate output");
			// TODO: Error
			return output_none;
		}
	}

	if (words->size == 0) {
		if (output_none != NULL) {
			strcpy(output_none, "I am utterly speechless!");
		}
		return output_none;
	}

	length = 1;
	for (i = 0; i < words->size; ++i) {
		length += words->entry[i].length;
	}

	output = (char *)realloc(output, sizeof(char) * length);

	if (output == NULL) {
		//error("make_output", "Unable to reallocate output.");
		//TODO: Error
		if (output_none != NULL) {
			strcpy(output_none, "I forgot what I was going to say!");
		}

		return output_none;
	}

	length = 0;

	for (i = 0; i < words->size; ++i) {
		for (j = 0; j < words->entry[i].length; ++j) {
			output[length++] = words->entry[i].word[j];
		}
	}

	output[length] = '\0';

	return output;
}

static float
evaluate_reply(MODEL *model, DICTIONARY *keys, DICTIONARY *words)
{
	register unsigned int i;
	register int j;
	register int k;
	int symbol;
	float probability;
	int count;
	float entropy = 0.0f;
	TREE *node;
	int num = 0;

	if (words->size <= 0) {
		return 0.0f;
	}

	initialize_context(model);
	model->context[0] = model->forward;

	for (i = 0; i < words->size; ++i) {
		symbol=find_word(model->dictionary, words->entry[i]);

		if (find_word(keys, words->entry[i]) != 0) {
			probability = 0.0f;
			count = 0;
			++num;

			for (j = 0; j < model->order; ++j) {
				if (model->context[j] != NULL) {
					node = find_symbol(model->context[j], symbol);
					probability += (float)(node->count) / (float)(model->context[j]->usage);
					++count;
				}
			}

			if (count > 0.0) {
				entropy -= (float)log(probability / (float)count);
			}
		}

		update_context(model, symbol);
	}

	initialize_context(model);
	model->context[0] = model->backward;

	for (k = words->size - 1; k >= 0; --k) {
		symbol = find_word(model->dictionary, words->entry[k]);

		if (find_word(keys, words->entry[k]) != 0) {
			probability = 0.0f;
			count = 0;
			++num;

			for (j=0; j<model->order; ++j) {
				if (model->context[j]!=NULL) {
					node = find_symbol(model->context[j], symbol);
					probability += (float)(node->count) / (float)(model->context[j]->usage);
					++count;
				}
			}

			if (count > 0) {
				entropy -= (float)log(probability / (float)count);
			}
		}

		update_context(model, symbol);
	}

	if (num >= 8) {
		entropy /= (float)sqrt(num - 1);
	}

	if (num>=16) {
		entropy /= (float)num;
	}

	return entropy;
}

static DICTIONARY *
reply(MODEL *model, DICTIONARY *keys)
{
	static DICTIONARY *replies = NULL;
	register int i;
	int symbol;
	bool start = true;

	if (replies == NULL) {
		replies = new_dictionary();
	}

	free_dictionary(replies);

	/* Start off by making sure that the model's context is empty. */
	initialize_context(model);
	model->context[0] = model->forward;
	used_key = false;

	/* Generate the reply in the forward direction. */
	while (1) {
		/* Get a random symbol from the current context. */
		if (start == true) {
			symbol = seed(model, keys);
		} else {
			symbol = babble(model, keys, replies);
		}

		if ((symbol == 0) || (symbol == 1)) {
			break;
		}

		start = false;

		/* Append the symbol to the reply dictionary. */
		if (replies->entry == NULL) {
			replies->entry = (STRING *)malloc((replies->size + 1) * sizeof(STRING));
		} else {
			replies->entry=(STRING *)realloc(replies->entry, (replies->size + 1) * sizeof(STRING));
		}

		if (replies->entry == NULL) {
			//error("reply", "Unable to reallocate dictionary");
			// TODO: error
			return NULL;
		}

		replies->entry[replies->size].length = model->dictionary->entry[symbol].length;
		replies->entry[replies->size].word = model->dictionary->entry[symbol].word;
		replies->size += 1;

		/* Extend the current context of the model with the current symbol. */
		update_context(model, symbol);
	}

	/* Start off by making sure that the model's context is empty. */
	initialize_context(model);
	model->context[0] = model->backward;

	/* Re-create the context of the model from the current reply dictionary
	 * so that we can generate backwards to reach the beginning of the
	 * string. */
	if (replies->size > 0) {
		for (i = MIN(replies->size - 1, model->order); i >= 0; --i) {
			symbol = find_word(model->dictionary, replies->entry[i]);
			update_context(model, symbol);
		}
	}

	/* Generate the reply in the backward direction. */
	while (1) {
		/* Get a random symbol from the current context. */
		symbol = babble(model, keys, replies);

		if ((symbol == 0) || (symbol == 1)) {
			break;
		}

		/* Prepend the symbol to the reply dictionary. */
		if (replies->entry == NULL) {
			replies->entry = (STRING *)malloc((replies->size + 1) * sizeof(STRING));
		} else {
			replies->entry = (STRING *)realloc(replies->entry, (replies->size + 1) * sizeof(STRING));
		}

		if (replies->entry==NULL) {
			//error("reply", "Unable to reallocate dictionary");
			//TODO: error
			return NULL;
		}

		/* Shuffle everything up for the prepend. */
		for (i = replies->size; i > 0; --i) {
			replies->entry[i].length = replies->entry[i - 1].length;
			replies->entry[i].word = replies->entry[i - 1].word;
		}

		replies->entry[0].length = model->dictionary->entry[symbol].length;
		replies->entry[0].word = model->dictionary->entry[symbol].word;
		replies->size += 1;

		/* Extend the current context of the model with the current symbol. */
		update_context(model, symbol);
	}

	return replies;
}

static int
seed(MODEL *model, DICTIONARY *keys)
{
	register unsigned int i;
	int symbol;
	unsigned int stop;

	/* Fix, thanks to Mark Tarrabain */
	if (model->context[0]->branch == 0) {
		symbol= 0;
	} else {
		symbol = model->context[0]->tree[rnd(model->context[0]->branch)]->symbol;
	}

	if (keys->size > 0) {
		i = rnd(keys->size);
		stop = i;
		while (1) {
			if ((find_word(model->dictionary, keys->entry[i]) != 0) &&
			    (find_word(aux, keys->entry[i]) == 0)) {
				symbol = find_word(model->dictionary, keys->entry[i]);
				return symbol;
			}

			++i;

			if (i == keys->size) {
				i = 0;
			}

			if (i == stop) {
				return symbol;
			}
		}
	}

	return symbol;
}

static int
rnd(int range)
{
	static bool flag = false;

	if (flag == false) {
		srand48(time(NULL));
	}

	flag = true;
	return floor(drand48() * (double)range);
}

static int
babble(MODEL *model, DICTIONARY *keys, DICTIONARY *words)
{
	TREE *node;
	register int i;
	int count;
	int symbol = 0;

	node = NULL;

	/* Select the longest available context. */
	for (i = 0; i <= model->order; ++i) {
		if (model->context[i] != NULL) {
			node=model->context[i];
		}
	}

	if (node->branch == 0) {
		return 0;
	}

	/* Choose a symbol at random from this context. */
	i = rnd(node->branch);
	count = rnd(node->usage);
	while (count >= 0) {
		/* If the symbol occurs as a keyword, then use it.  Only use an
		 * auxilliary keyword if a normal keyword has already been used. */
		symbol = node->tree[i]->symbol;

		if ((find_word(keys, model->dictionary->entry[symbol]) != 0) &&
		    ((used_key == true) ||
		     (find_word(aux, model->dictionary->entry[symbol]) == 0)) &&
		    (word_exists(words, model->dictionary->entry[symbol]) == false)) {
			used_key = true;
			break;
		}

		count -= node->tree[i]->count;
		i = (i >= (node->branch - 1)) ? 0 : i + 1;
	}

	return symbol;
}

static bool
word_exists(DICTIONARY *dictionary, STRING word)
{
	register unsigned int i;

	for (i = 0; i<dictionary->size; ++i) {
		if (wordcmp(dictionary->entry[i], word) == 0) {
			return true;
		}
	}

	return false;
}

static void
add_key(MODEL *model, DICTIONARY *keys, STRING word)
{
	int symbol;

	symbol = find_word(model->dictionary, word);

	if (symbol == 0) {
		return;
	}

	if (isalnum(word.word[0]) == 0) {
		return;
	}

	symbol = find_word(ban, word);
	if (symbol != 0) {
		return;
	}

	symbol = find_word(aux, word);
	if (symbol != 0) {
		return;
	}

	add_word(keys, word);
}

static void
add_aux(MODEL *model, DICTIONARY *keys, STRING word)
{
	int symbol;

	symbol = find_word(model->dictionary, word);
	if (symbol == 0) {
		return;
	}

	if (isalnum(word.word[0]) == 0) {
		return;
	}

	symbol = find_word(aux, word);
	if (symbol == 0) {
		return;
	}

	add_word(keys, word);
}

static void
save_model(char *modelname, MODEL *model)
{
	FILE *file;
	static char *filename=NULL;

	if (filename == NULL) {
		filename = (char *)malloc(sizeof(char) * 1);
	}

	/* Allocate memory for the filename */
	filename = (char *)realloc(filename, sizeof(char) * (strlen(directory) + strlen(SEP) + 12));

	if (filename == NULL) {
		// TODO: error
		// error("save_model","Unable to allocate filename");
	}

	if (filename == NULL) {
		return;
	}

	sprintf(filename, "%s%smegahal.brn", directory, SEP);
	file = fopen(filename, "wb");

	if (file == NULL) {
		//warn("save_model", "Unable to open file `%s'", filename);
		//TODO: warn
		return;
	}

	fwrite(COOKIE, sizeof(char), strlen(COOKIE), file);
	fwrite(&(model->order), sizeof(uint8_t), 1, file);
	save_tree(file, model->forward);
	save_tree(file, model->backward);
	save_dictionary(file, model->dictionary);

	fclose(file);
}

static void
save_tree(FILE *file, TREE *node)
{
	register unsigned int i;

	fwrite(&(node->symbol), sizeof(uint16_t), 1, file);
	fwrite(&(node->usage), sizeof(uint32_t), 1, file);
	fwrite(&(node->count), sizeof(uint16_t), 1, file);
	fwrite(&(node->branch), sizeof(uint16_t), 1, file);

	for (i = 0; i < node->branch; ++i) {
		save_tree(file, node->tree[i]);
	}
}

static void
save_dictionary(FILE *file, DICTIONARY *dictionary)
{
	register unsigned int i;

	fwrite(&(dictionary->size), sizeof(uint32_t), 1, file);

	for (i = 0; i < dictionary->size; ++i) {
		save_word(file, dictionary->entry[i]);
	}
}

static void
capitalize(char *string)
{
	register unsigned int i;
	bool start = true;

	for (i = 0; i < strlen(string); ++i) {
		if (isalpha(string[i])) {
			if (start == true) {
				string[i] = (char)toupper((int)string[i]);
			} else {
				string[i] = (char)tolower((int)string[i]);
			}

			start = false;
		}

		if ((i > 2) && (strchr("!.?", string[i - 1]) != NULL) &&
		    (isspace(string[i]))) {
			start = true;
		}
	}
}

static void
train(MODEL *model, char *filename)
{
	FILE *file;
	char buffer[1024];
	DICTIONARY *words = NULL;
	int length;

	if (filename == NULL) {
		return;
	}

	file = fopen(filename, "r");

	if (file == NULL) {
		//printf("Unable to find the personality %s\n", filename);
		//TODO: errro
		return;
	}

	fseek(file, 0, 2);
	length = ftell(file);
	rewind(file);

	words = new_dictionary();

	while (!feof(file)) {
		if (fgets(buffer, 1024, file) == NULL) {
			break;
		}

		if (buffer[0]=='#') {
			continue;
		}

		buffer[strlen(buffer) - 1]='\0';

		upper(buffer);
		make_words(buffer, words);
		learn(model, words);
	}

	free_dictionary(words);
	fclose(file);
}

