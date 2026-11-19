/* SPDX-License-Identifier: Apache-2.0
 * h3scan.c - exhaustive scans for the block-length-3 entropy constant h_3 over F_3.
 * MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
 * Pre-registration: notes/prereg-h3scan.md. Reference code: h3scan.py.
 *
 * For P: F_3^3 -> F_3^3 and F_t(x) = P(x) + t x, S(P) = sum_t sum_fibres s log2 s.
 * S(P) > 162 for one P would beat the KLSS base 1.889882 (README Theorem 2).
 *
 * Usage:
 *   h3scan quad L00 L01 L02 L10 L11 L12 L20 L21 L22   all 3^18 quadratic parts, linear part L
 *   h3scan s3                                          all 3^18 S_3-equivariant maps
 *   h3scan cyc                                         all 3^16 cyclic maps, degree <= 3
 *   h3scan evalquad L00 .. L22 c1 c2 c3 | evals3 f | evalcyc c      score of one map
 * Output lines: ABOVE/NEAR <tag> <enc..> <S>, TOP <tag> <S> <count> <enc..>, TOTAL, COUNTS.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

static int XC[27][3];
static double SLOG[28];
static int VP[28][9];
static const int PRIMES[9] = {2, 3, 5, 7, 11, 13, 17, 19, 23};

#define NTOP 8
static double top_val[NTOP];
static long long top_cnt[NTOP];
static char top_enc[NTOP][64];
static int ntop = 0;
static long long n_total = 0, n_above = 0, n_equal = 0, n_near = 0;
static int printed_above = 0, printed_near = 0;
static const char *mode_tag = "";

static void init_tables(void) {
  for (int i = 0; i < 27; i++) {
    XC[i][0] = i / 9; XC[i][1] = (i / 3) % 3; XC[i][2] = i % 3;
  }
  SLOG[0] = 0.0;
  for (int s = 1; s <= 27; s++) SLOG[s] = (double)s * log2((double)s);
  for (int s = 0; s <= 27; s++) {
    for (int p = 0; p < 9; p++) VP[s][p] = 0;
    if (s == 0) continue;
    int r = s;
    for (int p = 0; p < 9; p++) {
      while (r % PRIMES[p] == 0) { r /= PRIMES[p]; VP[s][p]++; }
    }
  }
}

static double eval_codes(unsigned char code[3][27], int hist[3][27]) {
  double S = 0.0;
  for (int t = 0; t < 3; t++) {
    int *h = hist[t];
    for (int v = 0; v < 27; v++) h[v] = 0;
    for (int x = 0; x < 27; x++) h[code[t][x]]++;
    for (int v = 0; v < 27; v++) S += SLOG[h[v]];
  }
  return S;
}

/* 0 iff prod_t prod_F |F|^|F| == 2^162 exactly */
static int exact_not_equal(int hist[3][27]) {
  long long e[9] = {0, 0, 0, 0, 0, 0, 0, 0, 0};
  for (int t = 0; t < 3; t++)
    for (int v = 0; v < 27; v++) {
      int s = hist[t][v];
      for (int p = 0; p < 9; p++) e[p] += (long long)s * VP[s][p];
    }
  if (e[0] != 162) return 1;
  for (int p = 1; p < 9; p++) if (e[p] != 0) return 1;
  return 0;
}

static inline double gate(void) {
  double g = (ntop < NTOP) ? -1.0 : top_val[ntop - 1] - 1e-9;
  double h = 162.0 - 1e-7;
  return g < h ? g : h;
}

static void update_top(double S, const char *enc) {
  for (int i = 0; i < ntop; i++) {
    if (fabs(top_val[i] - S) < 1e-9) { top_cnt[i]++; return; }
  }
  if (ntop == NTOP && !(S > top_val[NTOP - 1])) return;
  int pos = (ntop < NTOP) ? ntop : NTOP - 1;
  if (ntop < NTOP) ntop++;
  top_val[pos] = S; top_cnt[pos] = 1;
  strncpy(top_enc[pos], enc, 63); top_enc[pos][63] = 0;
  while (pos > 0 && top_val[pos] > top_val[pos - 1]) {
    double tv = top_val[pos]; top_val[pos] = top_val[pos - 1]; top_val[pos - 1] = tv;
    long long tc = top_cnt[pos]; top_cnt[pos] = top_cnt[pos - 1]; top_cnt[pos - 1] = tc;
    char te[64];
    memcpy(te, top_enc[pos], 64); memcpy(top_enc[pos], top_enc[pos - 1], 64);
    memcpy(top_enc[pos - 1], te, 64);
    pos--;
  }
}

static void record(double S, int hist[3][27], const char *enc) {
  if (S > 162.0 - 1e-7) {
    if (!exact_not_equal(hist)) {
      n_equal++;
    } else if (S > 162.0 + 1e-9) {
      n_above++;
      if (printed_above < 20) { printf("ABOVE %s %s %.12f\n", mode_tag, enc, S); printed_above++; }
    } else {
      n_near++;
      if (printed_near < 20) { printf("NEAR %s %s %.12f\n", mode_tag, enc, S); printed_near++; }
    }
  }
  update_top(S, enc);
}

static void finish(void) {
  printf("TOTAL %s %lld\n", mode_tag, n_total);
  printf("COUNTS %s %lld %lld %lld\n", mode_tag, n_above, n_equal, n_near);
  for (int i = 0; i < ntop; i++) printf("TOP %s %.12f %lld %s\n", mode_tag, top_val[i], top_cnt[i], top_enc[i]);
  fflush(stdout);
}

/* ------------------------------------------------------------ quadratic */
static unsigned char QVAL[729][27];

static void init_qval(void) {
  for (int c = 0; c < 729; c++) {
    int d[6], cc = c;
    for (int i = 0; i < 6; i++) { d[i] = cc % 3; cc /= 3; }
    for (int x = 0; x < 27; x++) {
      int x1 = XC[x][0], x2 = XC[x][1], x3 = XC[x][2];
      int m[6] = {x1 * x1, x2 * x2, x3 * x3, x1 * x2, x1 * x3, x2 * x3};
      int s = 0;
      for (int i = 0; i < 6; i++) s += d[i] * m[i];
      QVAL[c][x] = (unsigned char)(s % 3);
    }
  }
}

static void lin_table(int L[3][3], unsigned char lin[3][3][27]) {
  for (int t = 0; t < 3; t++)
    for (int i = 0; i < 3; i++)
      for (int x = 0; x < 27; x++) {
        int s = 0;
        for (int j = 0; j < 3; j++) s += (L[i][j] + (i == j ? t : 0)) * XC[x][j];
        lin[t][i][x] = (unsigned char)(s % 3);
      }
}

static unsigned char TAB3[3][729][27];

static void run_quad(int L[3][3]) {
  unsigned char lin[3][3][27];
  unsigned char part[3][27], code[3][27];
  int hist[3][27];
  char enc[64];
  lin_table(L, lin);
  for (int t = 0; t < 3; t++)
    for (int c = 0; c < 729; c++)
      for (int x = 0; x < 27; x++) TAB3[t][c][x] = (unsigned char)((QVAL[c][x] + lin[t][2][x]) % 3);
  for (int c1 = 0; c1 < 729; c1++) {
    for (int c2 = 0; c2 < 729; c2++) {
      for (int t = 0; t < 3; t++)
        for (int x = 0; x < 27; x++)
          part[t][x] = (unsigned char)(9 * ((QVAL[c1][x] + lin[t][0][x]) % 3)
                                      + 3 * ((QVAL[c2][x] + lin[t][1][x]) % 3));
      for (int c3 = 0; c3 < 729; c3++) {
        for (int t = 0; t < 3; t++) {
          const unsigned char *tb = TAB3[t][c3];
          for (int x = 0; x < 27; x++) code[t][x] = (unsigned char)(part[t][x] + tb[x]);
        }
        double S = eval_codes(code, hist);
        n_total++;
        if (S > gate()) {
          snprintf(enc, sizeof enc, "%d %d %d", c1, c2, c3);
          record(S, hist, enc);
        }
      }
    }
  }
}

static double eval_map(int P[27][3]) {
  unsigned char code[3][27];
  int hist[3][27];
  for (int t = 0; t < 3; t++)
    for (int x = 0; x < 27; x++) {
      int v[3];
      for (int i = 0; i < 3; i++) v[i] = (P[x][i] + t * XC[x][i]) % 3;
      code[t][x] = (unsigned char)(9 * v[0] + 3 * v[1] + v[2]);
    }
  return eval_codes(code, hist);
}

/* ------------------------------------------------------------ S_3-equivariant */
static int pair_index(int a, int b) {
  if (a > b) { int t = a; a = b; b = t; }
  if (a == 0) return b;
  if (a == 1) return 2 + b;
  return 5;
}

static int AIDX[27][3];

static void init_aidx(void) {
  for (int x = 0; x < 27; x++) {
    int x1 = XC[x][0], x2 = XC[x][1], x3 = XC[x][2];
    AIDX[x][0] = 6 * x1 + pair_index(x2, x3);
    AIDX[x][1] = 6 * x2 + pair_index(x1, x3);
    AIDX[x][2] = 6 * x3 + pair_index(x1, x2);
  }
}

static void run_s3(void) {
  int f[18];
  unsigned char code[3][27];
  int hist[3][27];
  char enc[64];
  long long total = 1;
  for (int i = 0; i < 18; i++) { f[i] = 0; total *= 3; }
  for (long long n = 0; n < total; n++) {
    for (int t = 0; t < 3; t++)
      for (int x = 0; x < 27; x++) {
        int v0 = (f[AIDX[x][0]] + t * XC[x][0]) % 3;
        int v1 = (f[AIDX[x][1]] + t * XC[x][1]) % 3;
        int v2 = (f[AIDX[x][2]] + t * XC[x][2]) % 3;
        code[t][x] = (unsigned char)(9 * v0 + 3 * v1 + v2);
      }
    double S = eval_codes(code, hist);
    n_total++;
    if (S > gate()) {
      snprintf(enc, sizeof enc, "%lld", n);
      record(S, hist, enc);
    }
    for (int d = 0; d < 18; d++) { if (++f[d] < 3) break; f[d] = 0; }
  }
}

static void s3_build(long long n, int P[27][3]) {
  int f[18];
  for (int i = 0; i < 18; i++) { f[i] = (int)(n % 3); n /= 3; }
  for (int x = 0; x < 27; x++)
    for (int i = 0; i < 3; i++) P[x][i] = f[AIDX[x][i]];
}

/* ------------------------------------------------------------ cyclic, degree <= 3 */
static int NMON = 0;
static int MVAL[16][27];
static int SIG[27], SIG2[27];

static int ipow(int v, int e) { int r = 1; for (int i = 0; i < e; i++) r *= v; return r; }

static void init_cyc(void) {
  NMON = 0;
  for (int a = 0; a < 3; a++)
    for (int b = 0; b < 3; b++)
      for (int c = 0; c < 3; c++) {
        int s = a + b + c;
        if (s < 1 || s > 3) continue;
        for (int x = 0; x < 27; x++)
          MVAL[NMON][x] = (ipow(XC[x][0], a) * ipow(XC[x][1], b) * ipow(XC[x][2], c)) % 3;
        NMON++;
      }
  for (int x = 0; x < 27; x++) SIG[x] = 9 * XC[x][1] + 3 * XC[x][2] + XC[x][0];
  for (int x = 0; x < 27; x++) SIG2[x] = SIG[SIG[x]];
}

static void run_cyc(void) {
  int cf[16], fx[27];
  unsigned char code[3][27];
  int hist[3][27];
  char enc[64];
  long long total = 1;
  for (int i = 0; i < NMON; i++) { cf[i] = 0; total *= 3; }
  for (int x = 0; x < 27; x++) fx[x] = 0;
  for (long long n = 0; n < total; n++) {
    for (int t = 0; t < 3; t++)
      for (int x = 0; x < 27; x++) {
        int v0 = (fx[x] + t * XC[x][0]) % 3;
        int v1 = (fx[SIG[x]] + t * XC[x][1]) % 3;
        int v2 = (fx[SIG2[x]] + t * XC[x][2]) % 3;
        code[t][x] = (unsigned char)(9 * v0 + 3 * v1 + v2);
      }
    double S = eval_codes(code, hist);
    n_total++;
    if (S > gate()) {
      snprintf(enc, sizeof enc, "%lld", n);
      record(S, hist, enc);
    }
    for (int d = 0; d < NMON; d++) {
      cf[d]++;
      for (int x = 0; x < 27; x++) fx[x] = (fx[x] + MVAL[d][x]) % 3;
      if (cf[d] < 3) break;
      cf[d] = 0;
    }
  }
}

static void cyc_build(long long n, int P[27][3]) {
  int fx[27];
  for (int x = 0; x < 27; x++) fx[x] = 0;
  for (int d = 0; d < NMON; d++) {
    int c = (int)(n % 3); n /= 3;
    for (int x = 0; x < 27; x++) fx[x] = (fx[x] + c * MVAL[d][x]) % 3;
  }
  for (int x = 0; x < 27; x++) { P[x][0] = fx[x]; P[x][1] = fx[SIG[x]]; P[x][2] = fx[SIG2[x]]; }
}

/* ------------------------------------------------------------ main */
static int read_L(char **argv, int L[3][3]) {
  for (int i = 0; i < 9; i++) {
    int v = atoi(argv[i]);
    if (v < 0 || v > 2) return 0;
    L[i / 3][i % 3] = v;
  }
  return 1;
}

int main(int argc, char **argv) {
  init_tables();
  init_qval();
  init_aidx();
  init_cyc();
  if (argc < 2) { fprintf(stderr, "usage: see header\n"); return 2; }
  const char *mode = argv[1];
  if (strcmp(mode, "quad") == 0) {
    int L[3][3];
    if (argc != 11 || !read_L(argv + 2, L)) { fprintf(stderr, "quad needs 9 digits\n"); return 2; }
    mode_tag = "quad";
    run_quad(L);
    finish();
  } else if (strcmp(mode, "s3") == 0) {
    mode_tag = "s3";
    run_s3();
    finish();
  } else if (strcmp(mode, "cyc") == 0) {
    mode_tag = "cyc";
    run_cyc();
    finish();
  } else if (strcmp(mode, "evalquad") == 0) {
    int L[3][3], P[27][3];
    if (argc != 14 || !read_L(argv + 2, L)) { fprintf(stderr, "evalquad needs 12 numbers\n"); return 2; }
    int c[3] = {atoi(argv[11]), atoi(argv[12]), atoi(argv[13])};
    for (int x = 0; x < 27; x++)
      for (int i = 0; i < 3; i++) {
        int s = QVAL[c[i]][x];
        for (int j = 0; j < 3; j++) s += L[i][j] * XC[x][j];
        P[x][i] = s % 3;
      }
    printf("S %.12f\n", eval_map(P));
  } else if (strcmp(mode, "evals3") == 0) {
    int P[27][3];
    if (argc != 3) return 2;
    s3_build(atoll(argv[2]), P);
    printf("S %.12f\n", eval_map(P));
  } else if (strcmp(mode, "evalcyc") == 0) {
    int P[27][3];
    if (argc != 3) return 2;
    cyc_build(atoll(argv[2]), P);
    printf("S %.12f\n", eval_map(P));
  } else {
    fprintf(stderr, "unknown mode\n");
    return 2;
  }
  return 0;
}
