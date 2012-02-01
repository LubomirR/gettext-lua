/* xgettext Lua backend.
   Copyright (C) 2012 Free Software Foundation, Inc.

   This file was written by Ľubomír Remák <lubomirr@lubomirr.eu>, 2012.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

/* Specification.  */
#include "x-lua.h"

#include <errno.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

#include "message.h"
#include "xgettext.h"
#include "error.h"
#include "xalloc.h"
#include "gettext.h"
#include "po-charset.h"

#define _(s) gettext(s)

#define SIZEOF(a) (sizeof(a) / sizeof(a[0]))

/* If true extract all strings.  */
static bool extract_all = false;

/* A hash table for keywords. */
static hash_table keywords;
static bool default_keywords = true;

/* Set extract_all flag (gettext will extract all strings). */
void
x_lua_extract_all ()
{
  extract_all = true;
}

/* Adds a keyword. Copied from other lexers. */
void
x_lua_keyword (const char *name)
{
  if (name == NULL)
    default_keywords = false;
  else
    {
      const char *end;
      struct callshape shape;
      const char *colon;

      if (keywords.table == NULL)
        hash_init (&keywords, 100);

      split_keywordspec (name, &end, &shape);

      /* The characters between name and end should form a valid C identifier.
         A colon means an invalid parse in split_keywordspec().  */
      colon = strchr (name, ':');
      if (colon == NULL || colon >= end)
        insert_keyword_callshape (&keywords, name, end - name, &shape);
    }
}

/* Finish initializing the keywords hash table.
   Called after argument processing, before each file is processed.  */
static void
init_keywords ()
{
  if (default_keywords)
    {
      /* When adding new keywords here, also update the documentation in
         xgettext.texi!  */
      x_lua_keyword ("_");
      x_lua_keyword ("gettext.gettext");
      x_lua_keyword ("gettext.dgettext:2");
      x_lua_keyword ("gettext.dcgettext:2");
      x_lua_keyword ("gettext.ngettext:1,2");
      x_lua_keyword ("gettext.dngettext:2,3");
      x_lua_keyword ("gettext.dcngettext:2,3");
      default_keywords = false;
    }
}

void
init_flag_table_lua ()
{
  xgettext_record_flag ("_:1:pass-lua-format");
  xgettext_record_flag ("gettext.gettext:1:pass-lua-format");
  xgettext_record_flag ("gettext.dgettext:2:pass-lua-format");
  xgettext_record_flag ("gettext.dcgettext:2:pass-lua-format");
  xgettext_record_flag ("gettext.ngettext:1:pass-lua-format");
  xgettext_record_flag ("gettext.ngettext:2:pass-lua-format");
  xgettext_record_flag ("gettext.dngettext:2:pass-lua-format");
  xgettext_record_flag ("gettext.dngettext:3:pass-lua-format");
  xgettext_record_flag ("gettext.dcngettext:2:pass-lua-format");
  xgettext_record_flag ("gettext.dcngettext:3:pass-lua-format");
  xgettext_record_flag ("string.format:1:lua-format");
}

/* ======================== Reading of characters.  ======================== */


/* Real filename, used in error messages about the input file.  */
static const char *real_file_name;

/* Logical filename and line number, used to label the extracted messages.  */
static char *logical_file_name;
static int line_number;

/* The input file stream.  */
static FILE *fp;


/* 1. line_number handling.  */

static unsigned char phase1_pushback[2];
static int phase1_pushback_length;

static int first_character = 1;

static int
phase1_getc ()
{
  int c;

  if (phase1_pushback_length)
    c = phase1_pushback[--phase1_pushback_length];
  else
    {
      c = getc (fp);

      if (first_character)
        {
          first_character = 0;

          /* Ignore shebang line. No pushback required in this case. */
          if (c == '#')
            {
              while (c != '\n' && c != EOF)
                {
                  c = getc (fp);
                }
              if (c == '\n')
                {
                  line_number++;
                  c = getc (fp);
                }
            }
        }


      if (c == EOF)
        {
          if (ferror (fp))
            error (EXIT_FAILURE, errno, _("error while reading \"%s\""),
                   real_file_name);
          return EOF;
        }

    }

  if (c == '\n')
    line_number++;

  return c;
}

/* Supports 2 characters of pushback. */

static void
phase1_ungetc (int c)
{
  if (c != EOF)
    {
      if (c == '\n')
        --line_number;

      if (phase1_pushback_length == SIZEOF (phase1_pushback))
        abort ();
      phase1_pushback[phase1_pushback_length++] = c;
    }
}


/* Accumulating comments.  */

/*TODO Check if necessary.*/
static int last_comment_line;
static int last_non_comment_line;

/* Comment buffer. */
static char *buffer;
/* Allocated buffer length. */
static size_t bufmax;
/* Used buffer length. */
static size_t buflen;

/* Comment handling functions, taken from other lexers. */

static inline void
comment_start ()
{
  buflen = 0;
}

static inline void
comment_add (int c)
{
  if (buflen >= bufmax)
    {
      bufmax = 2 * bufmax + 10;
      buffer = xrealloc (buffer, bufmax);
    }
  buffer[buflen++] = c;
}

static inline void
comment_line_end (size_t chars_to_remove)
{
  buflen -= chars_to_remove;
  while (buflen >= 1
         && (buffer[buflen - 1] == ' ' || buffer[buflen - 1] == '\t'))
    --buflen;
  if (chars_to_remove == 0 && buflen >= bufmax)
    {
      bufmax = 2 * bufmax + 10;
      buffer = xrealloc (buffer, bufmax);
    }
  buffer[buflen] = '\0';
  savable_comment_add (buffer);
}

/* Eats characters until \n and adds them to the comment. */
static void
eat_comment_line ()
{
  int c = 0;
  for (;;)
    {
      c = phase1_getc ();
      if (c == '\n' || c == EOF)
        {
          comment_line_end (0);
          break;
        }

      if (!(buflen == 0 && (c == ' ' || c == '\t')))
        {
          comment_add (c);
        }
    }
}

/* Comments. */

static int
phase2_getc ()
{
  int c;
  int lineno;

  c = phase1_getc ();

  if (c == '-')
    {
      c = phase1_getc ();

      if (c == '-')
        {
          /*
             It starts with --, so it must be either a short or a long comment.
           */
          c = phase1_getc ();

          if (c == '[')
            {
              c = phase1_getc ();

              int esigns = 0;
              while (c == '=')
                {
                  esigns++;
                  c = phase1_getc ();
                }

              if (c == '[')
                {
                  /* Long comment. */
                  bool right_bracket = false;
                  bool end = false;
                  int esigns2 = 0;

                  comment_start ();
                  while (!end)
                    {
                      c = phase1_getc ();

                      if (c == EOF)
                        {
                          break;
                        }

                      /* Ignore leading spaces and tabs. */
                      if (buflen == 0 && (c == ' ' || c == '\t'))
                        {
                          continue;
                        }

                      comment_add (c);

                      switch (c)
                        {
                        case ']':
                          if (!right_bracket)
                            {
                              right_bracket = true;
                              esigns2 = 0;
                            }
                          else
                            {
                              if (esigns2 == esigns)
                                {
                                  comment_line_end (2 + esigns);
                                  end = true;
                                }
                            }
                          break;

                        case '=':
                          if (right_bracket)
                            {
                              esigns2++;
                            }
                          break;

                        case '\n':
                          comment_line_end (1);
                          comment_start ();
                          lineno = line_number;
                          /* Intentionally not breaking. */

                        default:
                          right_bracket = false;
                        }
                    }
                  last_comment_line = lineno;
                  return ' ';
                }
              else
                {
                  /* One line (short) comment. */

                  phase1_ungetc (c);

                  comment_start ();
                  comment_add ('[');
                  while (esigns--)
                    {
                      comment_add ('=');
                    }
                  eat_comment_line ();
                  last_comment_line = lineno;
                  return '\n';
                }
            }
          else
            {
              /* One line (short) comment. */

              /* Add current character to the comment. */
              comment_start ();
              /* Unget current character. */
              phase1_ungetc (c);
              /* Eat the rest of the line. */
              eat_comment_line ();
              last_comment_line = lineno;
              return '\n';
            }
        }
      else
        {
          /* Minus sign */
          phase1_ungetc (c);
          return '-';
        }
    }
  else
    {
      return c;
    }
}

static flag_context_list_table_ty *flag_context_list_table;

enum token_type_ty
{
  token_type_eof,
  token_type_lparen,		/* ( */
  token_type_rparen,		/* ) */
  token_type_lbracket,		/* [ */
  token_type_rbracket,		/* ] */
  token_type_comma,		/* , */
  token_type_dot,		/* . */
  token_type_doubledot,		/* .. */
  token_type_operator1,		/* + - * / % not # - ^ */
  token_type_operator2,		/* < > <= >= ~= == */
  token_type_string,
  token_type_number,
  token_type_symbol,
  token_type_other
};

typedef enum token_type_ty token_type_ty;

/* static const char *token_names[] =
{
  "EOF",
  "LPAREN",
  "RPAREN",
  "LBRACKET",
  "RBRACKET",
  "DOUBLEDOT",
  "OPERATOR1",
  "OPERATOR2",
  "STRING",
  "NUMBER",
  "SYMBOL",
  "OTHER"
}; */

/* Taken from other lexers... */
typedef struct token_ty token_ty;
struct token_ty
{
  token_type_ty type;
  char *string;	                       /* for token_type_string_literal, token_type_symbol */
  refcounted_string_list_ty *comment;  /* for token_type_string_literal */
  int line_number;
};

/* Taken from other lexers... */
/* Free the memory pointed to by a 'struct token_ty'.  */
static inline void
free_token (token_ty * tp)
{
  if (tp->type == token_type_string || tp->type == token_type_symbol)
    free (tp->string);
  if (tp->type == token_type_string)
    drop_reference (tp->comment);
}

/* Our current string. */
static int string_buf_length;
static int string_buf_alloc;
static char *string_buf;

static void
string_start ()
{
  string_buf_length = 0;
}

static void
string_add (int c)
{
  if (string_buf_length >= string_buf_alloc)
    {
      string_buf_alloc = 2 * string_buf_alloc + 10;
      string_buf = xrealloc (string_buf, string_buf_alloc);
    }

  string_buf[string_buf_length++] = c;
}

static void
string_end ()
{
  string_buf[string_buf_length] = '\0';
}


/* We need 3 pushback tokens for string optimization. */
static int phase3_pushback_length;
static token_ty phase3_pushback[3];


static void
phase3_unget (token_ty * tok)
{

  if (tok->type != token_type_eof)
    {
      if (phase3_pushback_length == SIZEOF (phase3_pushback))
        abort ();
      phase3_pushback[phase3_pushback_length++] = *tok;
    }
}

static void
phase3_get (token_ty * tok)
{

  int c;
  int c2;
  int c_start;

  if (phase3_pushback_length)
    {
      *tok = phase3_pushback[--phase3_pushback_length];
      return;
    }

  tok->string = NULL;

  for (;;)
    {
      tok->line_number = line_number;
      c = phase2_getc ();

      switch (c)
        {
        case EOF:
          tok->type = token_type_eof;
          return;

        case '\n':
          if (last_non_comment_line > last_comment_line)
            {
              savable_comment_reset ();
            }
          /* Intentionally not breaking. */
        case ' ':
        case '\t':
        case '\r':
          continue;
        case '+':
        case '-':
        case '*':
        case '/':
        case '^':
        case '%':
        case '#':
          tok->type = token_type_operator1;
          return;
        case '<':
        case '>':
        case '=':
          c2 = phase1_getc ();
          if (c2 != '=')
            {
              phase1_ungetc (c2);
            }
          tok->type = token_type_operator2;
          return;
        case '~':
          c2 = phase1_getc ();
          if (c2 == '=')
            {
              tok->type = token_type_operator2;
              return;
            }
          else
            {
              phase1_ungetc (c2);
            }
          continue;
        case '(':
          tok->type = token_type_lparen;
          return;
        case ')':
          tok->type = token_type_rparen;
          return;
        case ',':
          tok->type = token_type_comma;
          return;

        case ';':
          tok->type = token_type_other;
          return;

          /*
             There are three operators beginning with a dot. Dot, double dot and tripple dot.
             The most useful for us is the concatenation operator (double dot).
           */
        case '.':
          c = phase1_getc ();
          if (c == '.')
            {
              c = phase1_getc ();
              if (c == '.')
                {
                  tok->type = token_type_other;
                  return;
                }
              else
                {
                  phase1_ungetc (c);
                  tok->type = token_type_doubledot;
                  return;
                }
            }
          else if (c >= '0' && c <= '9')
            {
              /* It's a number. We aren't interested in the actual numeric value, so ignore the dot and let next iteration eat the number. */
              phase1_ungetc (c);
              continue;
            }
          else
            {
              phase1_ungetc (c);
              tok->type = token_type_dot;
              return;
            }

        case '"':
        case '\'':
          c_start = c;
          string_start ();

          for (;;)
            {
              /* We need unprocessed characters from phase 1. */
              c = phase1_getc ();

              /* We got \, this is probably an escape sequence... */
              if (c == '\\')
                {
                  c = phase1_getc ();
                  switch (c)
                    {
                    case 'a':
                      string_add ('\a');
                      break;
                    case 'b':
                      string_add ('\b');
                      break;
                    case 'f':
                      string_add ('\f');
                      break;
                    case 'n':
                      string_add ('\n');
                      break;
                    case 'r':
                      string_add ('\r');
                      break;
                    case 't':
                      string_add ('\t');
                      break;
                    case 'v':
                      string_add ('\v');
                      break;

                    default:
                      /* Check if it's a \ddd sequence. */
                      if (c >= '0' && c <= '9')
                        {
                          int num = 0;
                          int i = 0;

                          while (c >= '0' && c <= '9' && i < 3)
                            {
                              num *= 10;
                              num += (c - '0');
                              c = phase1_getc ();
                              i++;
                            }

                          /* The last read character is either a non-number or another number after our \ddd sequence. We need to ungetc it. */
                          phase1_ungetc (c);

                          /* The sequence number is too big, this causes a lexical error. Ignore it. */
                          if (num < 256)
                            {
                              string_add (num);
                            }
                        }
                      else
                        {
                          string_add (c);
                        }
                    }
                }
              else if (c == c_start || c == EOF || c == '\n')
                {
                  /* End of string */
                  string_end ();
                  tok->string = xstrdup (string_buf);
                  tok->comment = add_reference (savable_comment);
                  tok->type = token_type_string;
                  return;
                }
              else
                {
                  string_add (c);
                }
            }
          break;

        case '[':
          c = phase1_getc ();

          /* Count the number of eq signs. */
          int esigns = 0;
          while (c == '=')
            {
              esigns++;
              c = phase1_getc ();
            }

          if (c != '[')
            {
              /* We did not find what we were looking for, ungetc it. */
              phase1_ungetc (c);
              if (esigns == 0)
                {
                  /* Our current character isn't [ and we got 0 eq signs, so the first [ must have been a left bracket. */
                  tok->type = token_type_lbracket;
                  return;
                }
              else
                {
                  /* Lexical error, ignore it. */
                  continue;
                }
            }

          string_start ();

          for (;;)
            {
              c = phase1_getc ();

              if (c == ']')
                {
                  /* We found a right bracket... */
                  c = phase1_getc ();

                  /* Count the number of eq signs. */
                  int esigns2 = 0;
                  while (c == '=')
                    {
                      esigns2++;
                      c = phase1_getc ();
                    }

                  if (c == ']' && esigns == esigns2)
                    {
                      /*
                         If our current character is ], we got ]==...==].
                         If the number of eq signs matches the number of eq signs in the opening long bracket,
                         we have found a string.
                       */
                      string_end ();
                      tok->string = xstrdup (string_buf);
                      tok->comment = add_reference (savable_comment);
                      tok->type = token_type_string;
                      return;
                    }
                  else
                    {
                      /*
                         Otherwise we got either ]==garbage or ]==...==] with a different number of eq signs.
                         We add ] and eq signs to the string and ungetc the current character,
                         because the second ] might be a part of another closing long bracket, e.g. '==]===]'.
                       */
                      phase1_ungetc (c);

                      string_add (']');
                      while (esigns2--)
                        {
                          string_add ('=');
                        }
                    }

                }
              else
                {
                  if (c == EOF)
                    {
                      string_end ();
                      tok->string = xstrdup (string_buf);
                      tok->comment = add_reference (savable_comment);
                      tok->type = token_type_string;
                      return;
                    }
                  else
                    {
                      string_add (c);
                    }
                }
            }
          break;

        case ']':
          tok->type = token_type_rbracket;
          return;

        default:
          if (c >= '0' && c <= '9')
            {
              while (c >= '0' && c <= '9')
                {
                  c = phase1_getc ();
                }

              if (c == '.')
                {
                  c = phase1_getc ();
                  while (c >= '0' && c <= '9')
                    {
                      c = phase1_getc ();
                    }
                }

              if (c == 'e' || c == 'E')
                {
                  if (c == '+' || c == '-')
                    {
                      c = phase1_getc ();
                    }
                  while (c >= '0' && c <= '9')
                    {
                      c = phase1_getc ();
                    }
                }

              phase1_ungetc (c);

              tok->type = token_type_number;
              return;
            }
          else if ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
                   || c == '_')
            {
              string_start ();
              while ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
                     || c == '_' || (c >= '0' && c <= '9'))
                {
                  string_add (c);
                  c = phase1_getc ();
                }
              string_end ();
              phase1_ungetc (c);

              if (strcmp (string_buf, "not") == 0)
                {
                  tok->type = token_type_operator1;
                }
              else if (strcmp (string_buf, "and") == 0)
                {
                  tok->type = token_type_operator2;
                }
              else if (strcmp (string_buf, "or") == 0)
                {
                  tok->type = token_type_operator2;
                }
              else
                {
                  tok->string = xstrdup (string_buf);
                  tok->type = token_type_symbol;
                }
              return;
            }
          else
            {
              tok->type = token_type_other;
            }
        }
    }
}

/*
  String optimization.
*/

static token_type_ty phase4_last;

/* We need 3 pushback tokens for module concatenation. */
static int phase4_pushback_length;
static token_ty phase4_pushback[3];

static void
phase4_unget (token_ty * tok)
{
  if (tok->type != token_type_eof)
    {
      if (phase4_pushback_length == SIZEOF (phase4_pushback))
        {
          abort ();
        }
      phase4_pushback[phase4_pushback_length++] = *tok;
    }
}

static void
phase4_get (token_ty * tok)
{

  if (phase4_pushback_length)
    {
      *tok = phase4_pushback[--phase4_pushback_length];
      phase4_last = tok->type;
      return;
    }

  token_ty toks[4];

  /* Get a token. */
  phase3_get (&toks[0]);

  /* Check if it's a string. */
  if (toks[0].type == token_type_string)
    {
      /* Check if the previous token wasn't an unallowed token. */
      if (phase4_last != token_type_operator1 && phase4_last != token_type_dot
          && phase4_last != token_type_symbol
          && phase4_last != token_type_doubledot
          && phase4_last != token_type_rparen)
        {
          for (;;)
            {
              /* Get another token. */
              phase3_get (&toks[1]);

              /* This has to be the concatenation operator. */
              if (toks[1].type == token_type_doubledot)
                {
                  phase3_get (&toks[2]);

                  /* Another string... */
                  if (toks[2].type == token_type_string)
                    {
                      phase3_get (&toks[3]);

                      /* Check if next token isn't an unallowed operator. */
                      if (toks[3].type != token_type_operator1)
                        {
                          size_t str1_len = strlen (toks[0].string);
                          size_t str2_len = strlen (toks[2].string);

                          /* Resize the first string. */
                          toks[1].string =
                            xrealloc (toks[0].string,
                                      str1_len + str2_len + 1);
                          /* Copy the current string to the end. */
                          memcpy (toks[1].string + str1_len, toks[2].string,
                                  str2_len + 1);

                          /* Destroy tokens. */
                          free_token (&toks[1]);
                          free_token (&toks[2]);

                          phase3_unget (&toks[3]);

                          continue;
                        }
                      phase3_unget (&toks[3]);
                    }
                  phase3_unget (&toks[2]);
                }
              phase3_unget (&toks[1]);
              break;
            }
        }
    }

  *tok = toks[0];

  phase4_last = tok->type;
}

static void
phase5_get (token_ty * tok)
{
  token_ty toks[3];

  /* Get a token. */
  phase4_get (&toks[0]);

  if (toks[0].type == token_type_symbol)
    {
      for (;;)
        {
          phase4_get (&toks[1]);
          if (toks[1].type == token_type_dot)
            {
              phase4_get (&toks[2]);
              if (toks[2].type == token_type_symbol)
                {
                  size_t str1_len = strlen (toks[0].string);
                  size_t str2_len = strlen (toks[2].string);

                  /* Resize the first string. */
                  toks[0].string =
                    xrealloc (toks[0].string, str1_len + str2_len + 1 + 1);
                  /* Copy the current string to the end. */
                  toks[0].string[str1_len] = '.';
                  memcpy (toks[0].string + str1_len + 1, toks[2].string,
                          str2_len + 1);

                  /* Destroy tokens. */

                  free_token (&toks[1]);
                  free_token (&toks[2]);

                  continue;
                }
              phase4_unget (&toks[2]);
            }
          phase4_unget (&toks[1]);
          break;
        }
    }

  *tok = toks[0];
}

static void
x_lua_lex (token_ty * tok)
{
  phase5_get (tok);
}

/*
  Extract following sequences:

  keyword '(' ... msgid ... ')'
  keyword msgid

*/
static bool
extract_balanced (message_list_ty * mlp, token_type_ty delim,
                  flag_context_ty outer_context,
                  flag_context_list_iterator_ty context_iter,
                  struct arglist_parser *argparser)
{

  /* Current argument number. */
  int arg = 1;

  /* Current callshape. */
  const struct callshapes *shape = NULL;

  /* Parsing state... */
  enum
  {
    no_keyword,
    keyword_found
  } state;

  token_ty tok;

  /* Context iterator that will be used if the next token is a '('.  */
  flag_context_list_iterator_ty next_context_iter =
    passthrough_context_list_iterator;
  /* Current context.  */
  flag_context_ty inner_context =
    inherited_context (outer_context,
                       flag_context_list_iterator_advance (&context_iter));

  for (;;)
    {
      x_lua_lex (&tok);

      switch (tok.type)
        {
        case token_type_symbol:
        {
          void *cs = NULL;

          /* Try to find this symbol in the keyword hash table. If it's found, set the value as our current callshape. */
          if (hash_find_entry
              (&keywords, tok.string, strlen (tok.string), &cs) == 0)
            {
              shape = (const struct callshapes *) cs;
              state = keyword_found;
            }
          else
            {
              state = no_keyword;
            }

          next_context_iter =
            flag_context_list_iterator (flag_context_list_table_lookup
                                        (flag_context_list_table,
                                         tok.string, strlen (tok.string)));
          free (tok.string);
          continue;
        }

        case token_type_lparen:
          /* Found left parenthesis, recursive call. */
          if (extract_balanced
              (mlp, token_type_rparen, inner_context, next_context_iter,
               arglist_parser_alloc (mlp,
                                     state == keyword_found ? shape : NULL)))
            {
              arglist_parser_done (argparser, arg);
              return true;
            }
          next_context_iter = null_context_list_iterator;
          state = 0;
          break;

        case token_type_rparen:
          /*
             We got ')'. If "delim" is set to ')', we have successfully finished processing this part.
             If "delim" is set to EOF, we found an unmatched ')'. Ignore it.
           */
          if (delim == token_type_rparen || delim == token_type_eof)
            {
              arglist_parser_done (argparser, arg);
              return false;
            }

          next_context_iter = null_context_list_iterator;
          state = no_keyword;
          continue;

        case token_type_lbracket:
          /* Found left bracket, recursive call. */
          if (extract_balanced
              (mlp, token_type_rbracket, null_context,
               null_context_list_iterator, arglist_parser_alloc (mlp, NULL)))
            {
              arglist_parser_done (argparser, arg);
              return true;
            }
          next_context_iter = null_context_list_iterator;
          state = 0;
          break;

        case token_type_rbracket:
          /*
             We got ']'. If "delim" is set to ']', we have successfully finished processing this part.
             If "delim" is set to EOF, we found an unmatched ']'. Ignore it.
           */
          if (delim == token_type_rbracket || delim == token_type_eof)
            {
              arglist_parser_done (argparser, arg);
              return false;
            }

          next_context_iter = null_context_list_iterator;
          state = no_keyword;
          continue;

        case token_type_comma:
          arg++;
          inner_context =
            inherited_context (outer_context,
                               flag_context_list_iterator_advance
                               (&context_iter));
          next_context_iter = passthrough_context_list_iterator;
          state = no_keyword;
          continue;

        case token_type_eof:
          arglist_parser_done (argparser, arg);
          return true;

        case token_type_string:
        {
          lex_pos_ty pos;
          pos.file_name = logical_file_name;
          pos.line_number = tok.line_number;

          if (extract_all)
            {
              remember_a_message (mlp, NULL, tok.string, inner_context,
                                  &pos, NULL, tok.comment);
            }
          else
            {
              if (state == keyword_found)
                {
                  struct arglist_parser *tmp_argparser;
                  tmp_argparser = arglist_parser_alloc (mlp, shape);

                  arglist_parser_remember (tmp_argparser, 1, tok.string,
                                           inner_context, pos.file_name,
                                           pos.line_number, tok.comment);
                  arglist_parser_done (tmp_argparser, 1);
                }
              else
                {
                  arglist_parser_remember (argparser, arg, tok.string,
                                           inner_context, pos.file_name,
                                           pos.line_number, tok.comment);
                }
            }
        }
        drop_reference (tok.comment);
        next_context_iter = null_context_list_iterator;
        state = 0;
        continue;

        case token_type_dot:
        case token_type_operator1:
        case token_type_operator2:
        case token_type_number:
        case token_type_other:
          next_context_iter = null_context_list_iterator;
          state = no_keyword;
          continue;

        default:
          abort ();
        }
    }
}

void
extract_lua (FILE * f,
             const char *real_filename, const char *logical_filename,
             flag_context_list_table_ty * flag_table,
             msgdomain_list_ty * mdlp)
{
  message_list_ty *mlp = mdlp->item[0]->messages;

  fp = f;
  real_file_name = real_filename;
  logical_file_name = xstrdup (logical_filename);
  line_number = 1;

  last_comment_line = -1;
  last_non_comment_line = -1;

  flag_context_list_table = flag_table;

  init_keywords ();

  while (!extract_balanced
         (mlp, token_type_eof, null_context, null_context_list_iterator,
          arglist_parser_alloc (mlp, NULL)));

  /* Close scanner.  */
  fp = NULL;
  real_file_name = NULL;
  logical_file_name = NULL;
  line_number = 0;
}
