/*------------------------------------------------------------------------*/
/* Copyright (C) 2014-2014, Armin Biere, Johannes Kepler University, Linz */
/*------------------------------------------------------------------------*/

#include <stdio.h>
#include <assert.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>

void die (const char * fmt, ...) {
  va_list ap;
  fputs ("*** cheskol: ", stderr);
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  exit (1);
}

static const char * name;

void perr (const char * fmt, ...) {
  va_list ap;
  fprintf (stderr, "*** parse error in '%s': ", name);
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  exit (1);
}

void msg (const char * fmt, ...) {
  va_list ap;
  fputs ("c [cheskol] ", stdout);
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

static int V, C;
static int M, I, L, O, A, MAX;
static int *Q;

typedef struct AIG {
  unsigned isinput : 1, isand : 1, isconstant : 1;
  union { int lhs, lit; };
  int rhs0, rhs1, uql;
} AIG;

static AIG * aig;
static int * skol;

static int * cnf, szcnf, ncnf;

#define NEW(P,N) \
do { \
  size_t B = (N) * sizeof *(P); \
  (P) = malloc (B); memset ((P), 0, (B)); \
} while (0)

static long steps;

static int uql (int lit) {
  int idx, res, l, r;
  AIG * a;
  steps++;
  assert (0 <= lit), assert (lit <= MAX);
  if (lit <= 1) return 1;
  a = aig + (idx = lit/2);
  assert (!a->isconstant);
  if (a->isinput) {
    assert (idx <= V);
    res = Q[idx];
    assert (res < 0);
    res = -res;
    assert (res > 1);
    return res;
  }
  assert (a->isand);
  if ((res = a->uql)) return res;
  l = uql (a->rhs0);
  r = uql (a->rhs1);
  res = l < r ? r : l;
  assert (res > 0);
  a->uql = res;
  return res;
}

static int clslit (int i) {
  assert (0 <= i), assert (i < C);
  return V + i + 1;
}

static int truelit () { return V + C + 1; }

static int aiglit (int i) {
  int res;
  assert (0 <= i), assert (i <= MAX);
  if (i == 1) return truelit ();
  else if (!i) return -truelit ();
  res = truelit () + i/2;
  if (i & 1) res = -res;
  return res;
}

static int W, E;

static FILE * dfile;

static void unit (int lit) { 
  assert (lit), fprintf (dfile, "%d 0\n", lit), W++;
}

static void binary (int a, int b) {
  assert (a && b), fprintf (dfile, "%d %d 0\n", a, b), W++;
}

static void ternary (int a, int b, int c) {
  assert (a), assert (b), assert (c);
  fprintf (dfile, "%d %d %d 0\n", a, b, c);
  W++;
}

int main (int argc, char ** argv) {
  int ch, i, j, k, q, s, lit, e, a, u;
  int lhs, rhs0, rhs1, idx;
  FILE * qfile, * afile;
  AIG * and;
  if (argc > 1 && !strcmp (argv[1], "-h")) {
    printf ("usage: cheskol [-h] <qdimacs> <aag> [ <dimacs> ]\n");
    exit (0);
  }
  if (argc < 3 || argc > 4)
    die ("invalid number of %d command line options (try '-h')", argc - 1);
  if (!(qfile = fopen ((name = argv[1]), "r")))
    die ("failed to open QDIMACS file '%s' for reading", name);
  if (fscanf (qfile, "p cnf %d %d", &V, &C) != 2 || V < 0 || C < 0)
    perr ("invalid QDIMACS header");
  msg ("found QDIMACS header 'p cnf %d %d' in '%s'", V, C, name);
  NEW (Q, V + 1);
  s = q = 1;
  for (;;) {
    ch = getc (qfile);
    if (ch == ' ' || ch == '\n') continue;
    if (ch == 'a') s++, q = -1;
    else if (ch == 'e') s++, q = 1;
    else if (ch != EOF) { ungetc (ch, qfile); break; }
    else if (C) perr ("unexpected EOF after header (all clauses missing)");
    else break;
    for (;;) {
      if (fscanf (qfile, "%d", &lit) != 1) perr ("failed to read literal");
      if (!lit) break;
      if (lit < 0) perr ("negative quantified literal", lit);
      if (lit > V) perr ("literal too large", lit);
      if (Q[lit]) perr ("literal %d quantified twice", lit);
      Q[lit] = q * s;
    }
  }
  e = a = u = 0;
  for (i = 1; i <= V; i++) {
    if (Q[i] < 0) a++;
    else if (Q[i] > 0) e++;
    else u++;
  }
  msg ("found %d existential, %d universal, %d unquantified", e, a, u);
  i = 0;
  while (fscanf (qfile, " %d ", &lit) == 1) {
    if (ncnf == szcnf) {
      szcnf = szcnf ? 2*szcnf : 1;
      cnf = realloc (cnf, szcnf * sizeof *cnf);
    }
    cnf[ncnf++] = lit;
    if (!lit) i++;
  }
  if ((ch = getc (qfile)) != EOF) perr ("expected EOF after last literal");
  if (ncnf && cnf[ncnf]) perr ("terminating clause missing");
  if (i < C) perr ("not enough clauses");
  if (i > C) perr ("too many clauses");
  assert (C <= ncnf);
  msg ("parsed %d literals in %d clauses", ncnf - C, C);
  fclose (qfile);
  if (!(afile = fopen ((name = argv[2]), "r")))
    die ("failed to open AAG file '%s' for reading", name);
  if (fscanf (afile, "aag %d %d %d %d %d", &M,&I,&L,&O,&A) != 5 ||
      M < 0 || I < 0 || L || O < 0 || A < 0)
    perr ("invalid AAG header");
  msg ("found AAG header 'aag %d %d %d %d %d' in '%s'", M,I,L,O,A, name);
  if (a != I) perr ("num inputs %d does not match num universals %d", I, u);
  if (e != O) perr ("num outputs %d does not match num existentials %d", O, e);
  NEW (aig, M + 1);
  aig[0].isconstant = 1;
  MAX = 2*M + 1;
  for (i = 0; i < I; i++) {
    int idx;
    if (fscanf (afile, "%d", &lit) != 1 || (lit&1) || lit <= 1 || lit > MAX)
      perr ("invalid input literal %d", lit);
    if (aig[idx = lit/2].isinput)
      perr ("input literal %d specified twice", lit);
    if ((idx = lit/2) > V) die ("input literal %d too large for QBF", lit);
    if (!Q[idx]) die ("input literal %d unquantified", lit);
    if (Q[idx] > 0) die ("skolem literal %d existentially quantified", lit);
    aig[idx].isinput = 1;
    aig[idx].lit = lit;
  }
  msg ("parsed %d inputs", I);
  NEW (skol, O);
  for (i = 0; i < O; i++) {
    if (fscanf (afile, "%d", &lit) != 1 || lit < 0 || lit > MAX)
      perr ("invalid literal %d used as output %d", lit, i);
    if ((lit & 1)) die ("odd skolem literal %d", lit);
    if (lit < 2) die ("constant skolem literal %d", lit);
    if ((idx = lit/2) > V) die ("skolem literal %d too large for QBF", lit);
    if (!Q[idx]) die ("skolem literal %d unquantified", lit);
    if (Q[idx] < 0) die ("skolem literal %d universally quantified", lit);
    skol[i] = lit;
  }
  msg ("parsed %d outputs", O);
  for (i = 0; i < A; i++) {
    if (fscanf (afile, "%d %d %d", &lhs, &rhs0, &rhs1) != 3)
      perr ("failed to parse AND number %d", i);
    if (lhs <= 1 || lhs > MAX) perr ("invalid LHS %d in AND %d", lhs, i);
    if (rhs0 < 0 || rhs0 > MAX) perr ("invalid RHS %d in AND %d", rhs0, i);
    if (rhs1 < 0 || rhs1 > MAX) perr ("invalid RHS %d in AND %d", rhs1, i);
    and = aig + (idx = lhs/2);
    if (and->isinput) perr ("LHS %d of AND %d used as input", lhs, i);
    if (and->isand) perr ("LHS %d of AND %d used as LHS before", lhs, i);
    and->lhs = lhs, and->rhs0 = rhs0, and->rhs1 = rhs1;
    and->isand = 1;
  }
  msg ("parsed %d AND gates", A);
  fclose (afile);
  for (i = 0; i < O; i++) {
    int il, sl;
    idx = (lit = skol[i])/2;
    il = abs (Q[idx]);
    sl = uql (lit);
    if (sl <= il) continue;
    die ("failed dependency check for existential QBF variable %d", idx);
  }
  msg ("sucessfully checked %d skolem functions in %ld steps", O, steps);
  if (argc == 4) {
    if (!(dfile = fopen ((name = argv[3]), "w")))
      die ("failed to open DIMACS file '%s' for writing", name);
  } else dfile = stdout;

  E = (ncnf - C)	// binary clauses = number of literals
    + 1			// connecting clauses with additional clause lits
    + 1			// AIG unit clause
    + 3*A		// Tseitin clauses for each AND gate
    + 2*I		// connect universals with inputs
    + 2*O		// connect existentials with skolem functions
    ;

  fprintf (dfile, "p cnf %d %d\n", aiglit (2*M), E);
  i = j = 0;
  for (j = 0; j < ncnf; j = k + 1) {
    for (k = j; cnf[k]; k++)
      ;
    while (k > j)
      binary (-clslit (i), -cnf[--k]);
    for (k = j; cnf[k]; k++)
      ;
    i++;
  }
  assert (i == C);
  for (i = 0; i < C; i++) fprintf (dfile, "%d ", clslit (i));
  fprintf (dfile, "0\n"), W++;
  unit (truelit ());
  for (i = 1; i <= M; i++) {
    and = aig + i;
    if (and->isinput) assert (and->lit == 2*i);
    else if (and->isand) {
      assert (and->lhs == 2*i);
      binary (-aiglit (and->lhs), aiglit (and->rhs0));
      binary (-aiglit (and->lhs), aiglit (and->rhs1));
      ternary (aiglit (and->lhs), -aiglit (and->rhs0), -aiglit (and->rhs1));
    }
  }
  for (i = 1; i <= M; i++) {
    and = aig + i;
    if (!and->isinput) continue;
    lit = and->lit;
    assert (!(lit & 1));
    lhs = lit/2;
    assert (0 < lhs), assert (lhs <= V);
    assert (Q[lhs] < 0);
    binary (-lhs, aiglit (lit));
    binary (lhs, -aiglit (lit));
  }
  for (i = 0; i < O; i++) {
    lit = skol[i];
    assert (!(lit & 1));
    lhs = lit/2;
    assert (0 < lhs), assert (lhs <= V);
    assert (Q[lhs] > 0);
    binary (-lhs, aiglit (lit));
    binary (lhs, -aiglit (lit));
  }
  if (argc == 4) {
    fclose (dfile);
    msg ("finished writing %d clauses to '%s'", W, name);
  } else msg ("finished writing %d clauses to '<stdout>'", W);
  assert (W == E);
  free (aig);
  free (skol);
  free (Q);
  free (cnf);
  return 0;
}
