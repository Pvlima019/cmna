/*
 * Programa de Analise Nodal Modificada no Tempo Compacta
 * Por: Matheus Fernandes Moreno (matheus.moreno@poli.ufrj.br)
 *      Paulo Victor Sant'Anna Pedroso de Lima (pv019@poli.ufrj.br)
 * 
 * Baseado no programa de demonstracao de analise nodal modificada compacta
 * do professor Antonio Carlos M. de Queiroz.
 *
 * Universidade Federal do Rio de Janeiro - UFRJ
 * Circuitos Eletricos II - 2018.1
 * Professor: Antonio Carlos M. de Queiroz (acmq@coe.ufrj.br)
 * 
 * Versao 0.0.5:
 *   - Implementada a leitura do netlist e algumas funcoes do codigo base.
 *
 */

/*
 * Coisas a fazer:
 *
 * 0. Reestruturar o codigo do Moreirao
 * 1. Implementar a analise no tempo, sem absolutamente nenhum componente a mais
 * 1.1. Implementar o calculo do ponto de operacao
 * 2. Implementar as fontes de sinal
 * 3. Implementar os elementos reativos com o metodo theta
 * 4. Implementar os nao-lineares com NR
 * 5. Implementar um codigo em Python pra plotar os graficos para o relatorio
 * 6. Fazer o relatorio em LaTeX bem xeroso
 * 7. (opcional) Tentar fazer uma GUI
 *
 */


/* Elementos já implementados:
 *
 * Resistor:             R<nome> <no+> <no-> <resistencia>
 * Transcondutor:        G<nome> <noI+> <noI-> <nov+> <nov-> <Gm>
 * Amp. Operacional:     O<nome> <saida+> <saida-> <entrada+> <entrada->
 *
 * Elementos a serem implementados:
 *
 * Indutor:              L<nome> <no+> <no-> <indutancia>
 * Capacitor:            C<nome> <no+> <no-> <capacitancia>
 * Transf. Ideal:        K<nome> <noa> <nob> <noc> <nod> <n>
 * Amp. de Tensao:       E<nome> <noV+> <noV-> <nov+> <nov-> <Av>
 * Amp. de Corrente:     F<nome> <noI+> <noI-> <noi+> <noi-> <Ai>
 * Transresistor:        H<nome> <noV+> <noV-> <noi+> <noi-> <Rm>
 * Fonte de Tensao:      V<nome> <no+> <no-> <parametros>
 * Fonte de Corrente:    I<nome> <no+> <no-> <parametros>
 * Diodo:                D<nome> <no+> <no-> <Is> <nVt>
 * Transistor bipolar:   Q<nome> <noc> <nob> <noe> <tipo> <a> <ar> <Isbe> <nVtbe> <Isbc> <nVtbc>
 * 
 */


#ifdef _MSC_VER
#define _CRT_SECURE_NO_WARNINGS   // Impede que o VS reclame de algumas funcoes
#endif

#define versao "0.0.5 - 05/2018"

#include <stdio.h>
#include <conio.h>
#include <ctype.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#define MAX_LINHA     80          // Comprimento maximo de uma linha do netlist
#define MAX_NOME      11          // Comprimento maximo do nome de um elemento
#define MAX_ELEM      50          // Numero maximo de elementos no circuito
#define MAX_NOS       50          // Numero maximo de nos no circuito
#define TOLG        1e-9          // Tolerancia nas operacoes
#define C_PO         1e9          // Capacitor no ponto de operacao
#define L_PO        1e-9          // Indutor no ponto de operacao

#define DEBUG                     // #define para depuracao do codigo


typedef struct elemento {    // Elemento do netlist
  char nome[MAX_NOME];
  double valor;
  int a, b, c, d, x, y;
} elemento;

typedef int tabela[MAX_NOS + 1]; 


/* Declaracao de variaveis usadas no programa.
 * E mais simples usarmos globais para nao nos preocuparmos com ponteiros. */

elemento netlist[MAX_ELEM];

int
  ne,      // Elementos
  nv,      // Variaveis
  neq,     // Equacoes
  nn,      // Nos
  pPonto,  // Passos por ponto
  ii, jj, kk;

tabela C, L;    // Vetores para o algoritmo de compactacao

char
  nomeArquivo[MAX_NOME + 1],
  tipo,
  na[MAX_NOME], nb[MAX_NOME], nc[MAX_NOME], nd[MAX_NOME],
  lista[MAX_NOS + 1][MAX_NOME + 2],
  txt[MAX_LINHA + 1],
  *param;

FILE *arquivo;    // Arquivo com o netlist

double
  Yn[MAX_NOS + 1][MAX_NOS + 2],    // Matriz a ser resolvida
  tempo,   // Tempo de simulacao
  passo,   // Tamanho do passo
  theta;   // Valor de theta


/* Resolucao de sistema de equacoes lineares.
 * Metodo de Gauss-Jordan com condensacao pivotal. */
int
resolversistema(void) {
  int i, j, l, a;
  double t, p;

  for (i = 1; i <= neq; i++) {
    t = 0.0;
    a = i;
    
    for (l = i; l <= neq; l++) {
      if (fabs(Yn[l][i])>fabs(t)) {
        a = l;
        t = Yn[l][i];
      }
    }
    
    if (i != a) {
      for (l = 1; l <= neq + 1; l++) {
        p = Yn[i][l];
        Yn[i][l] = Yn[a][l];
        Yn[a][l] = p;
      }
    }
    
    if (fabs(t) < TOLG) {
      printf("(!) ERRO: Sistema singular\r\n");
      return 1;
    }
    
    for (j = neq + 1; j > i; j--) {  // Colocado j > i ao inves de j > 0. ver se funciona
      Yn[i][j] /= t;
      p = Yn[i][j];
      if (p != 0)
        for (l = 1; l <= neq; l++) {
          if (l != i)
            Yn[l][j] -= Yn[l][i] * p;
        }
    }
  }
  return 0;
}


/* Rotina que conta os nos e atribui numeros a eles. */
int
numeroNo(char *nome) {
  int i, achou;
  i = 0;
  achou = 0;
  
  while (!achou && i <= nv)
    if (!(achou = !strcmp(nome, lista[i])))
      i++;
  
  if (!achou) {
    if (nv == MAX_NOS) {
      printf("(!) ERRO: O programa so aceita ate %d nos.\r\n", nv);
      printf("Pressione qualquer tecla para sair...");
      _getch();
      exit(1);
    }
    nv++;
    strcpy(lista[nv], nome);
    return nv; // Novo no
  }
  
  return i; // No ja conhecido
}


/* Rotina de controle para que o numero de variaveis nao exceda o de nos. */
void
testarNos(void) {
  if (nv > MAX_NOS) {
    printf("(!) ERRO: As variaveis extra excederam o numero de variaveis permitido (%d).\r\n", MAX_NOS);
    printf("Pressione qualquer tecla para sair...");
    _getch();
    exit(1);
  }
}


/* Rotina que le o arquivo com o netlist e cria o vetor de componentes.
 * Tambem e feita a leitura dos parametros para a analise no tempo. */
void
lerNetlist() {
  do {
    ne = 0;
    nv = 0;
    strcpy(lista[0], "0");
    printf("Nome do arquivo com o netlist (ex: mna.net): ");
    scanf("%50s", nomeArquivo);
    arquivo = fopen(nomeArquivo, "r");
    if (arquivo == 0)
      printf("(!) ERRO: Arquivo %s inexistente.\r\n", nomeArquivo);
  } while (arquivo == 0);

  printf("Lendo netlist:\r\n");
  fgets(txt, MAX_LINHA, arquivo);
  printf("Titulo: %s", txt);

  while (fgets(txt, MAX_LINHA, arquivo)) {
    ne++;   // Nao usa o netlist[0]
    if (ne>MAX_ELEM) {
      printf("(!) ERRO: O programa so aceita ate %d elementos.\r\n", MAX_ELEM);
      printf("Pressione qualquer tecla para sair...");
      _getch();
      fclose(arquivo);
      exit(1);
    }
    
    txt[0] = toupper(txt[0]);    // O primeiro caractere da linha descreve a linha
    tipo = txt[0];
    sscanf(txt, "%10s", netlist[ne].nome);
    param = txt + strlen(netlist[ne].nome);

    if (tipo == 'R' || tipo == 'I' || tipo == 'V' || tipo == 'L' || tipo == 'C') {
      sscanf(param, "%10s %10s %lg", na, nb, &netlist[ne].valor);
      printf("%s %s %s %g\r\n", netlist[ne].nome, na, nb, netlist[ne].valor);
      netlist[ne].a = numeroNo(na);
      netlist[ne].b = numeroNo(nb);
    }
    else if (tipo == 'G' || tipo == 'E' || tipo == 'F' || tipo == 'H' || tipo == 'K') {
      sscanf(param, "%10s %10s %10s %10s %lg", na, nb, nc, nd, &netlist[ne].valor);
      printf("%s %s %s %s %s %g\r\n", netlist[ne].nome, na, nb, nc, nd, netlist[ne].valor);
      netlist[ne].a = numeroNo(na);
      netlist[ne].b = numeroNo(nb);
      netlist[ne].c = numeroNo(nc);
      netlist[ne].d = numeroNo(nd);
    }
    else if (tipo == 'O') {
      sscanf(param, "%10s %10s %10s %10s", na, nb, nc, nd);
      printf("%s %s %s %s %s\r\n", netlist[ne].nome, na, nb, nc, nd);
      netlist[ne].a = numeroNo(na);
      netlist[ne].b = numeroNo(nb);
      netlist[ne].c = numeroNo(nc);
      netlist[ne].d = numeroNo(nd);
    }
    else if (tipo == '*') {   // Comentario comeca com "*"
      printf("Comentario: %s\r", txt);
      ne--;
    }
    else if (tipo == '.') {
      sscanf(param, "%lg %lg %*s %lg %d", &tempo, &passo, &theta, &pPonto);
      printf("Tempo de simulacao: %gs\r\n", tempo);
      printf("Tamanho de Passo: %gs\r\n", passo);
      printf("Theta: %g\r\n", theta);
      printf("Passos por ponto na tabela: %d\r\n", pPonto);
      ne--;
    }
    else {
      printf("(!) ERRO: Elemento desconhecido: %s\r\n", txt);
      printf("Pressione qualquer tecla para sair...");
      _getch();
      fclose(arquivo);
      exit(1);
    }
  }
  fclose(arquivo);
}


/* Rotina de simplificacao do sistema com amp. ops. */
void
somar(int *Q, int a, int b) {
  int i, a1, b1;

  if (Q[a] > Q[b]) {
    a1 = Q[b];
    b1 = Q[a];
  }
  else {
    a1 = Q[a];
    b1 = Q[b];
  }
  
  if (a1 == b1) {
    printf("(!) ERRO: Circuito invalido - Entradas ou saidas de um amp. op. em curto.\r\n");
    printf("Pressione qualquer tecla para sair...\r\n");
    _getch();
    exit(1);
  }

  for (i = 1; i <= MAX_NOS; i++) {
    if (Q[i] == b1)
      Q[i] = a1;
    if (Q[i]>b1)
      Q[i]--;
  }
}

void
operacional(int na, int nb, int nc, int nd) {
#ifdef DEBUG
  printf("AMP OP: Saida: %d %d; entrada %d %d\r\n", na, nb, nc, nd);
#endif
  somar(L, na, nb);
  somar(C, nc, nd);
}

void
transcondutancia(double gm, int n1, int n2, int n3, int n4) {
  Yn[L[n1]][C[n3]] += gm;
  Yn[L[n2]][C[n4]] += gm;
  Yn[L[n1]][C[n4]] -= gm;
  Yn[L[n2]][C[n3]] -= gm;
}

void
condutancia(double g, int a, int b) {
  transcondutancia(g, a, b, a, b);
}

void
corrente(double i, int a, int b) {
  Yn[L[a]][neq + 1] -= i;
  Yn[L[b]][neq + 1] += i;
}

int
main() {
  system("cls");
  printf("Programa de Analise Nodal Modificada Compacta no Tempo\r\n");
  printf("Por Matheus F. Moreno e Paulo Victor S. Lima\r\n");
  printf("Codigo base por Antonio Carlos M. de Queiroz\r\n");
  printf("Versao %s\r\n", versao);

  for (ii = 0; ii <= MAX_NOS; ii++) {   // Inicializacao de tabelas
    C[ii] = ii;
    L[ii] = ii;
  }

  lerNetlist();  // Chamada da rotina que le o netlist
  _getch();

  return 0;
}
