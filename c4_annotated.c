// c4.c - C in four functions

// char, int, and pointer types
// if, while, return, and expression statements
// just enough features to allow self-compilation and a bit more

// Written by Robert Swierczek

#include <stdio.h>
#include <stdlib.h>
#include <memory.h>
#include <unistd.h>
#include <fcntl.h>
#define int long long

char *p, *lp, // current position in source code
     *data;   // data/bss pointer

int *e, *le,  // current position in emitted code
    *id,      // currently parsed identifier
    *sym,     // symbol table (simple list of identifiers)
    tk,       // current token
    ival,     // current token value
    ty,       // current expression type
    loc,      // local variable offset
    line,     // current line number
    src,      // print source and assembly flag
    debug;    // print executed instructions

//tokens and classes (operators last and in precedence order)
enum {
  Num = 128, Fun, Sys, Glo, Loc, Id,  //basic token types
  Char, Else, Enum, If, Int, Return, Sizeof, While,  //keywords
  Assign, Cond, Lor, Lan, Or, Xor, And, Eq, Ne, Lt, Gt, Le, Ge, Shl, Shr, Add, Sub, Mul, Div, Mod, Inc, Dec, Brak  //operators
};

//opcodes for the virtual machine
enum { LEA ,IMM ,JMP ,JSR ,BZ  ,BNZ ,ENT ,ADJ ,LEV ,LI  ,LC  ,SI  ,SC  ,PSH ,
       OR  ,XOR ,AND ,EQ  ,NE  ,LT  ,GT  ,LE  ,GE  ,SHL ,SHR ,ADD ,SUB ,MUL ,DIV ,MOD ,
       OPEN,READ,CLOS,PRTF,MALC,FREE,MSET,MCMP,EXIT };

//basic types
enum { CHAR, INT, PTR };

//identifier offsets (since we can't create an ident struct)
enum { Tk, Hash, Name, Class, Type, Val, HClass, HType, HVal, Idsz };

//function to get the next token from the source code
void next()
{
  char *pp;  //temporary pointer for identifiers and strings

  while (tk = *p) {  //loop through the source code character by character
    ++p;  //move to the next character

    if (tk == '\n') {  //handle newlines
      if (src) {  //if debugging is enabled, print the current line
        printf("%d: %.*s", line, p - lp, lp);
        lp = p;
        while (le < e) {  //print emitted assembly instructions
          printf("%8.4s", &"LEA ,IMM ,JMP ,JSR ,BZ  ,BNZ ,ENT ,ADJ ,LEV ,LI  ,LC  ,SI  ,SC  ,PSH ,"
                           "OR  ,XOR ,AND ,EQ  ,NE  ,LT  ,GT  ,LE  ,GE  ,SHL ,SHR ,ADD ,SUB ,MUL ,DIV ,MOD ,"
                           "OPEN,READ,CLOS,PRTF,MALC,FREE,MSET,MCMP,EXIT,"[*++le * 5]);
          if (*le <= ADJ) printf(" %d\n", *++le); else printf("\n");
        }
      }
      ++line;  //increment the line counter
    }
    else if (tk == '#') {  //skip preprocessor directives and comments
      while (*p != 0 && *p != '\n') ++p;  //ignore everything until newline
    }
    else if ((tk >= 'a' && tk <= 'z') || (tk >= 'A' && tk <= 'Z') || tk == '_') {
      //handle identifiers (variable names, function names, etc.)
      pp = p - 1;  //store start position
      while ((*p >= 'a' && *p <= 'z') || (*p >= 'A' && *p <= 'Z') || (*p >= '0' && *p <= '9') || *p == '_')
        tk = tk * 147 + *p++;  //generate a unique hash for the identifier
      tk = (tk << 6) + (p - pp);  //adjust the hash based on length to prevent collisions
      id = sym;  //search for the identifier in the symbol table
      while (id[Tk]) {  //loop through the existing identifiers
        if (tk == id[Hash] && !memcmp((char *)id[Name], pp, p - pp)) { tk = id[Tk]; return; }  //if found, return it
        id = id + Idsz;
      }
      id[Name] = (int)pp;  //store name in symbol table
      id[Hash] = tk;  //store computed hash
      tk = id[Tk] = Id;  //mark it as an identifier
      return;
    }
    else if (tk >= '0' && tk <= '9') {
      //handle numeric literals
      if (ival = tk - '0') { while (*p >= '0' && *p <= '9') ival = ival * 10 + *p++ - '0'; }  //decimal numbers
      else if (*p == 'x' || *p == 'X') {  //hexadecimal numbers
        while ((tk = *++p) && ((tk >= '0' && tk <= '9') || (tk >= 'a' && tk <= 'f') || (tk >= 'A' && tk <= 'F')))
          ival = ival * 16 + (tk & 15) + (tk >= 'A' ? 9 : 0);
      }
      else { while (*p >= '0' && *p <= '7') ival = ival * 8 + *p++ - '0'; }  //octal numbers
      tk = Num;
      return;
    }
    else if (tk == '/') {
      //handle division and comments
      if (*p == '/') {  //single-line comment
        ++p;
        while (*p != 0 && *p != '\n') ++p;
      }
      else {
        tk = Div;  //division operator
        return;
      }
    }
    else if (tk == '\'' || tk == '"') {
      //handle character and string literals
      pp = data;  //save pointer to store the data
      while (*p != 0 && *p != tk) {
        if ((ival = *p++) == '\\') {  //handle escape sequences
          if ((ival = *p++) == 'n') ival = '\n';  //newline escape sequence
        }
        if (tk == '"') *data++ = ival;  //store characters if it's a string
      }
      ++p;  //skip the closing quote
      if (tk == '"') ival = (int)pp; else tk = Num;  //store the string address
      return;
    }
    else if (tk == '=') { if (*p == '=') { ++p; tk = Eq; } else tk = Assign; return; }  //handle assignment and equality
    else if (tk == '+') { if (*p == '+') { ++p; tk = Inc; } else tk = Add; return; }  //handle addition and increment
    else if (tk == '-') { if (*p == '-') { ++p; tk = Dec; } else tk = Sub; return; }  //handle subtraction and decrement
    else if (tk == '!') { if (*p == '=') { ++p; tk = Ne; } return; }  //handle NOT and inequality
    else if (tk == '<') { if (*p == '=') { ++p; tk = Le; } else if (*p == '<') { ++p; tk = Shl; } else tk = Lt; return; }  //handle <, <=, <<
    else if (tk == '>') { if (*p == '=') { ++p; tk = Ge; } else if (*p == '>') { ++p; tk = Shr; } else tk = Gt; return; }  //handle >, >=, >>
    else if (tk == '|') { if (*p == '|') { ++p; tk = Lor; } else tk = Or; return; }  //handle | and ||
    else if (tk == '&') { if (*p == '&') { ++p; tk = Lan; } else tk = And; return; }  //handle & and &&
    else if (tk == '^') { tk = Xor; return; }  //handle XOR
    else if (tk == '%') { tk = Mod; return; }  //handle modulus
    else if (tk == '*') { tk = Mul; return; }  //handle multiplication
    else if (tk == '[') { tk = Brak; return; }  //handle array indexing
    else if (tk == '?') { tk = Cond; return; }  //handle ternary operator
    else if (tk == '~' || tk == ';' || tk == '{' || tk == '}' || tk == '(' || tk == ')' || tk == ']' || tk == ',' || tk == ':') return;  //single-character tokens
  }
}

//parse an expression based on operator precedence
void expr(int lev)
{
  int t, *d;  //temporary variable and pointer for storing intermediate results

  if (!tk) {  //check if token is empty (end of file reached unexpectedly)
    printf("%d: unexpected eof in expression\n", line);
    exit(-1);
  }
  else if (tk == Num) {  //handle numeric literals
    *++e = IMM;  //load immediate value
    *++e = ival;  //store the numeric value
    next();  //move to next token
    ty = INT;  //set type to integer
  }
  else if (tk == '"') {  //handle string literals
    *++e = IMM;  //load immediate value (address of the string)
    *++e = ival;  //store string value
    next();
    while (tk == '"') next();  //allow concatenated strings
    data = (char *)((int)data + sizeof(int) & -sizeof(int));  //align data pointer
    ty = PTR;  //type is pointer to char
  }
  else if (tk == Sizeof) {  //handle sizeof() operator
    next();
    if (tk == '(') next(); else { printf("%d: open paren expected in sizeof\n", line); exit(-1); }
    ty = INT;  //default type is int
    if (tk == Int) next();
    else if (tk == Char) { next(); ty = CHAR; }
    while (tk == Mul) { next(); ty = ty + PTR; }  //handle pointer types
    if (tk == ')') next(); else { printf("%d: close paren expected in sizeof\n", line); exit(-1); }
    *++e = IMM;
    *++e = (ty == CHAR) ? sizeof(char) : sizeof(int);  //return size of type
    ty = INT;
  }
  else if (tk == Id) {  //handle identifiers (variables and function calls)
    d = id;  //store identifier pointer
    next();
    if (tk == '(') {  //function call
      next();
      t = 0;  //argument count
      while (tk != ')') {  //parse function arguments
        expr(Assign);  //evaluate argument
        *++e = PSH;  //push argument
        ++t;  //increment argument count
        if (tk == ',') next();  //handle multiple arguments
      }
      next();
      if (d[Class] == Sys) *++e = d[Val];  //system function call
      else if (d[Class] == Fun) { *++e = JSR; *++e = d[Val]; }  //user-defined function call
      else { printf("%d: bad function call\n", line); exit(-1); }
      if (t) { *++e = ADJ; *++e = t; }  //adjust stack after function call
      ty = d[Type];  //set return type
    }
    else if (d[Class] == Num) {  //numeric constant
      *++e = IMM;
      *++e = d[Val];
      ty = INT;
    }
    else {  //variable access
      if (d[Class] == Loc) { *++e = LEA; *++e = loc - d[Val]; }  //local variable
      else if (d[Class] == Glo) { *++e = IMM; *++e = d[Val]; }  //global variable
      else { printf("%d: undefined variable\n", line); exit(-1); }
      *++e = ((ty = d[Type]) == CHAR) ? LC : LI;  //load value
    }
  }
  else if (tk == '(') {  //handle parentheses
    next();
    if (tk == Int || tk == Char) {  //handle type casting
      t = (tk == Int) ? INT : CHAR; next();
      while (tk == Mul) { next(); t = t + PTR; }
      if (tk == ')') next(); else { printf("%d: bad cast\n", line); exit(-1); }
      expr(Inc);
      ty = t;
    }
    else {
      expr(Assign);
      if (tk == ')') next(); else { printf("%d: close paren expected\n", line); exit(-1); }
    }
  }
  else if (tk == Mul) {  //handle pointer dereferencing
    next(); expr(Inc);
    if (ty > INT) ty = ty - PTR; else { printf("%d: bad dereference\n", line); exit(-1); }
    *++e = (ty == CHAR) ? LC : LI;
  }
  else if (tk == And) {  //handle address-of operator
    next(); expr(Inc);
    if (*e == LC || *e == LI) --e; else { printf("%d: bad address-of\n", line); exit(-1); }
    ty = ty + PTR;
  }
  else if (tk == '!') {  //handle logical NOT
    next();
    expr(Inc);
    *++e = PSH; *++e = IMM; *++e = 0; *++e = EQ;
    ty = INT;
  }
  else if (tk == '~') {  //handle bitwise NOT
    next();
    expr(Inc);
    *++e = PSH; *++e = IMM; *++e = -1; *++e = XOR;
    ty = INT;
  }
  else if (tk == Add) {  //handle unary plus (ignored)
    next();
    expr(Inc);
    ty = INT;
  }
  else if (tk == Sub) {  //handle unary minus
    next();
    *++e = IMM;
    if (tk == Num) { *++e = -ival; next(); }  //negative number
    else { *++e = -1; *++e = PSH; expr(Inc); *++e = MUL; }  //negate expression
    ty = INT;
  }
  else if (tk == Inc || tk == Dec) {  //handle pre-increment and pre-decrement
    t = tk;
    next();
    expr(Inc);
    if (*e == LC) { *e = PSH; *++e = LC; }  //load char variable
    else if (*e == LI) { *e = PSH; *++e = LI; }  //load int variable
    else { printf("%d: bad lvalue in pre-increment\n", line); exit(-1); }
    *++e = PSH;
    *++e = IMM; *++e = (ty > PTR) ? sizeof(int) : sizeof(char);
    *++e = (t == Inc) ? ADD : SUB;
    *++e = (ty == CHAR) ? SC : SI;
  }
  else { printf("%d: bad expression\n", line); exit(-1); }

  //precedence climbing algorithm (Top Down Operator Precedence)
  while (tk >= lev) {  
    t = ty;
    if (tk == Assign) {  //handle assignment
      next();
      if (*e == LC || *e == LI) *e = PSH; else { printf("%d: bad lvalue in assignment\n", line); exit(-1); }
      expr(Assign);
      *++e = ((ty = t) == CHAR) ? SC : SI;
    }
    else if (tk == Cond) {  //handle ternary operator (condition ? true_expr : false_expr)
      next();
      *++e = BZ; d = ++e;
      expr(Assign);
      if (tk == ':') next(); else { printf("%d: conditional missing colon\n", line); exit(-1); }
      *d = (int)(e + 3); *++e = JMP; d = ++e;
      expr(Cond);
      *d = (int)(e + 1);
    }
	
	//handle logical OR (||) operator
	else if (tk == Lor) { 
	  next();
	  *++e = BNZ;  //branch if nonzero
	  d = ++e;
	  expr(Lan);  //evaluate the next expression
	  *d = (int)(e + 1);  //patch jump address
	  ty = INT;
	}

	//handle logical AND (&&) operator
	else if (tk == Lan) { 
	  next();
	  *++e = BZ;  //branch if zero
	  d = ++e;
	  expr(Or);
	  *d = (int)(e + 1);
	  ty = INT;
	}

	//handle bitwise OR (|)
	else if (tk == Or)  { 
	  next();
	  *++e = PSH;  //push first operand
	  expr(Xor);
	  *++e = OR;  //perform bitwise OR
	  ty = INT;
	}

	//handle bitwise XOR (^)
	else if (tk == Xor) { 
	  next();
	  *++e = PSH;
	  expr(And);
	  *++e = XOR;  //perform bitwise XOR
	  ty = INT;
	}

	//handle bitwise AND (&)
	else if (tk == And) { 
	  next();
	  *++e = PSH;
	  expr(Eq);
	  *++e = AND;  //perform bitwise AND
	  ty = INT;
	}

	//handle equality (==)
	else if (tk == Eq)  { 
	  next();
	  *++e = PSH;
	  expr(Lt);
	  *++e = EQ;  //perform equality check
	  ty = INT;
	}

	//handle inequality (!=)
	else if (tk == Ne)  { 
	  next();
	  *++e = PSH;
	  expr(Lt);
	  *++e = NE;  //perform inequality check
	  ty = INT;
	}

	//handle less than (<)
	else if (tk == Lt)  { 
	  next();
	  *++e = PSH;
	  expr(Shl);
	  *++e = LT;  //perform less than comparison
	  ty = INT;
	}

	//handle greater than (>)
	else if (tk == Gt)  { 
	  next();
	  *++e = PSH;
	  expr(Shl);
	  *++e = GT;  //perform greater than comparison
	  ty = INT;
	}

	//handle less than or equal (<=)
	else if (tk == Le)  { 
	  next();
	  *++e = PSH;
	  expr(Shl);
	  *++e = LE;
	  ty = INT;
	}

	//handle greater than or equal (>=)
	else if (tk == Ge)  { 
	  next();
	  *++e = PSH;
	  expr(Shl);
	  *++e = GE;
	  ty = INT;
	}

	//handle shift left (<<)
	else if (tk == Shl) { 
	  next();
	  *++e = PSH;
	  expr(Add);
	  *++e = SHL;  //perform shift left
	  ty = INT;
	}

	//handle shift right (>>)
	else if (tk == Shr) { 
	  next();
	  *++e = PSH;
	  expr(Add);
	  *++e = SHR;  //perform shift right
	  ty = INT;
	}

	//handle addition (+)
	else if (tk == Add) {
	  next();
	  *++e = PSH;
	  expr(Mul);
	  if ((ty = t) > PTR) {  //if adding a pointer, scale appropriately
		*++e = PSH;
		*++e = IMM;
		*++e = sizeof(int);
		*++e = MUL;
	  }
	  *++e = ADD;  //perform addition
	}

	//handle subtraction (-)
	else if (tk == Sub) {
	  next();
	  *++e = PSH;
	  expr(Mul);
	  if (t > PTR && t == ty) {  //pointer subtraction
		*++e = SUB;
		*++e = PSH;
		*++e = IMM;
		*++e = sizeof(int);
		*++e = DIV;
		ty = INT;
	  }
	  else if ((ty = t) > PTR) {  //if subtracting a pointer, scale appropriately
		*++e = PSH;
		*++e = IMM;
		*++e = sizeof(int);
		*++e = MUL;
		*++e = SUB;
	  }
	  else *++e = SUB;  //regular subtraction
	}

	//handle multiplication (*)
	else if (tk == Mul) { 
	  next();
	  *++e = PSH;
	  expr(Inc);
	  *++e = MUL;  //perform multiplication
	  ty = INT;
	}

	//handle division (/)
	else if (tk == Div) { 
	  next();
	  *++e = PSH;
	  expr(Inc);
	  *++e = DIV;  //perform division
	  ty = INT;
	}

	//handle modulus (%)
	else if (tk == Mod) { 
	  next();
	  *++e = PSH;
	  expr(Inc);
	  *++e = MOD;  //perform modulus
	  ty = INT;
	}

	//handle post-increment and post-decrement (x++ / x--)
	else if (tk == Inc || tk == Dec) {
	  if (*e == LC) { *e = PSH; *++e = LC; }  //handle char
	  else if (*e == LI) { *e = PSH; *++e = LI; }  //handle int
	  else { printf("%d: bad lvalue in post-increment\n", line); exit(-1); }
	  *++e = PSH;
	  *++e = IMM; *++e = (ty > PTR) ? sizeof(int) : sizeof(char);
	  *++e = (tk == Inc) ? ADD : SUB;
	  *++e = (ty == CHAR) ? SC : SI;
	  *++e = PSH;
	  *++e = IMM; *++e = (ty > PTR) ? sizeof(int) : sizeof(char);
	  *++e = (tk == Inc) ? SUB : ADD;
	  next();
	}

	//handle array indexing (x[i])
	else if (tk == Brak) {
	  next();
	  *++e = PSH;
	  expr(Assign);
	  if (tk == ']') next(); else { printf("%d: close bracket expected\n", line); exit(-1); }
	  if (t > PTR) { *++e = PSH; *++e = IMM; *++e = sizeof(int); *++e = MUL;  }  //handle pointer indexing
	  else if (t < PTR) { printf("%d: pointer type expected\n", line); exit(-1); }
	  *++e = ADD;
	  *++e = ((ty = t - PTR) == CHAR) ? LC : LI;
	}

	//handle syntax errors
	else { printf("%d: compiler error tk=%d\n", line, tk); exit(-1); }
	}
}

//parse statements (if, while, return, blocks, and expressions)
void stmt()
{
  int *a, *b;  //temporary pointers for jump addresses

  if (tk == If) {  //handle if statement
    next();
    if (tk == '(') next(); else { printf("%d: open paren expected\n", line); exit(-1); }
    expr(Assign);
    if (tk == ')') next(); else { printf("%d: close paren expected\n", line); exit(-1); }
    *++e = BZ; b = ++e;
    stmt();
    if (tk == Else) {  //handle else clause
      *b = (int)(e + 3);
      *++e = JMP;
      b = ++e;
      next();
      stmt();
    }
    *b = (int)(e + 1);
  }
  else if (tk == While) {  //handle while loops
    next();
    a = e + 1;
    if (tk == '(') next(); else { printf("%d: open paren expected\n", line); exit(-1); }
    expr(Assign);
    if (tk == ')') next(); else { printf("%d: close paren expected\n", line); exit(-1); }
    *++e = BZ; b = ++e;
    stmt();
    *++e = JMP;
    *++e = (int)a;
    *b = (int)(e + 1);
  }
  else if (tk == Return) {  //handle return statements
    next();
    if (tk != ';') expr(Assign);
    *++e = LEV;
    if (tk == ';') next(); else { printf("%d: semicolon expected\n", line); exit(-1); }
  }
}

//entry point of the compiler and virtual machine
int main(int argc, char **argv)
{
  int fd, bt, ty, poolsz, *idmain;  //file descriptor, base type, type, memory pool size, main function pointer
  int *pc, *sp, *bp, a, cycle; //virtual machine registers
  int i, *t; //temporary variables

  --argc; ++argv;  //skip program name in arguments
  if (argc > 0 && **argv == '-' && (*argv)[1] == 's') { src = 1; --argc; ++argv; }  //enable source debugging
  if (argc > 0 && **argv == '-' && (*argv)[1] == 'd') { debug = 1; --argc; ++argv; }  //enable debug mode
  if (argc < 1) { printf("usage: c4 [-s] [-d] file ...\n"); return -1; }  //print usage if no file is given

  if ((fd = open(*argv, 0)) < 0) { printf("could not open(%s)\n", *argv); return -1; }  //open source file

  poolsz = 256*1024; //allocate memory pool (256 KB)
  if (!(sym = malloc(poolsz))) { printf("could not malloc(%d) symbol area\n", poolsz); return -1; }
  if (!(le = e = malloc(poolsz))) { printf("could not malloc(%d) text area\n", poolsz); return -1; }
  if (!(data = malloc(poolsz))) { printf("could not malloc(%d) data area\n", poolsz); return -1; }
  if (!(sp = malloc(poolsz))) { printf("could not malloc(%d) stack area\n", poolsz); return -1; }

  memset(sym,  0, poolsz);  //initialize symbol table
  memset(e,    0, poolsz);  //initialize text area
  memset(data, 0, poolsz);  //initialize data segment

  //add predefined keywords and functions to symbol table
  p = "char else enum if int return sizeof while "
      "open read close printf malloc free memset memcmp exit void main";
  i = Char; while (i <= While) { next(); id[Tk] = i++; } //add keywords
  i = OPEN; while (i <= EXIT) { next(); id[Class] = Sys; id[Type] = INT; id[Val] = i++; } //add system functions
  next(); id[Tk] = Char; //handle void type
  next(); idmain = id; //store reference to main function

  //read source file into memory
  if (!(lp = p = malloc(poolsz))) { printf("could not malloc(%d) source area\n", poolsz); return -1; }
  if ((i = read(fd, p, poolsz-1)) <= 0) { printf("read() returned %d\n", i); return -1; }
  p[i] = 0;
  close(fd);

  //parse declarations
  line = 1;
  next();
  while (tk) {
    bt = INT; //default base type is int
    if (tk == Int) next();
    else if (tk == Char) { next(); bt = CHAR; }
    else if (tk == Enum) {  //handle enum type
      next();
      if (tk != '{') next();
      if (tk == '{') {
        next();
        i = 0;
        while (tk != '}') {
          if (tk != Id) { printf("%d: bad enum identifier %d\n", line, tk); return -1; }
          next();
          if (tk == Assign) { next(); if (tk != Num) { printf("%d: bad enum initializer\n", line); return -1; } i = ival; next(); }
          id[Class] = Num; id[Type] = INT; id[Val] = i++;
          if (tk == ',') next();
        }
        next();
      }
    }
    while (tk != ';' && tk != '}') {
      ty = bt;
      while (tk == Mul) { next(); ty = ty + PTR; }  //handle pointers
      if (tk != Id) { printf("%d: bad global declaration\n", line); return -1; }
      if (id[Class]) { printf("%d: duplicate global definition\n", line); return -1; }
      next();
      id[Type] = ty;
      if (tk == '(') { //function definition
        id[Class] = Fun;
        id[Val] = (int)(e + 1);
        next(); i = 0;
        while (tk != ')') { //parse function parameters
          ty = INT;
          if (tk == Int) next();
          else if (tk == Char) { next(); ty = CHAR; }
          while (tk == Mul) { next(); ty = ty + PTR; }
          if (tk != Id) { printf("%d: bad parameter declaration\n", line); return -1; }
          if (id[Class] == Loc) { printf("%d: duplicate parameter definition\n", line); return -1; }
          id[HClass] = id[Class]; id[Class] = Loc;
          id[HType]  = id[Type];  id[Type] = ty;
          id[HVal]   = id[Val];   id[Val] = i++;
          next();
          if (tk == ',') next();
        }
        next();
        if (tk != '{') { printf("%d: bad function definition\n", line); return -1; }
        loc = ++i;
        next();
        while (tk == Int || tk == Char) { //parse local variables
          bt = (tk == Int) ? INT : CHAR;
          next();
          while (tk != ';') {
            ty = bt;
            while (tk == Mul) { next(); ty = ty + PTR; }
            if (tk != Id) { printf("%d: bad local declaration\n", line); return -1; }
            if (id[Class] == Loc) { printf("%d: duplicate local definition\n", line); return -1; }
            id[HClass] = id[Class]; id[Class] = Loc;
            id[HType]  = id[Type];  id[Type] = ty;
            id[HVal]   = id[Val];   id[Val] = ++i;
            next();
            if (tk == ',') next();
          }
          next();
        }
        *++e = ENT; *++e = i - loc; //enter function
        while (tk != '}') stmt(); //parse function body
        *++e = LEV; //leave function
        id = sym; //restore symbol table
        while (id[Tk]) {
          if (id[Class] == Loc) {
            id[Class] = id[HClass];
            id[Type] = id[HType];
            id[Val] = id[HVal];
          }
          id = id + Idsz;
        }
      }
      else { //global variable
        id[Class] = Glo;
        id[Val] = (int)data;
        data = data + sizeof(int);
      }
      if (tk == ',') next();
    }
    next();
  }

  if (!(pc = (int *)idmain[Val])) { printf("main() not defined\n"); return -1; }  //check if main() exists
  if (src) return 0;

  //setup stack
  bp = sp = (int *)((int)sp + poolsz);
  *--sp = EXIT; //call exit if main returns
  *--sp = PSH; t = sp;
  *--sp = argc;
  *--sp = (int)argv;
  *--sp = (int)t;

  //execute instructions
  cycle = 0;
  while (1) {
    i = *pc++; ++cycle;
    if (debug) { //print debug info
      printf("%d> %.4s", cycle, &"LEA ,IMM ,JMP ,JSR ,BZ  ,BNZ ,ENT ,ADJ ,LEV ,LI  ,LC  ,SI  ,SC  ,PSH ,"
                          "OR  ,XOR ,AND ,EQ  ,NE  ,LT  ,GT  ,LE  ,GE  ,SHL ,SHR ,ADD ,SUB ,MUL ,DIV ,MOD ,"
                          "OPEN,READ,CLOS,PRTF,MALC,FREE,MSET,MCMP,EXIT,"[i * 5]);
      if (i <= ADJ) printf(" %d\n", *pc); else printf("\n");
    }
	if      (i == LEA) a = (int)(bp + *pc++);                             // load local address
    else if (i == IMM) a = *pc++;                                         // load global address or immediate
    else if (i == JMP) pc = (int *)*pc;                                   // jump
    else if (i == JSR) { *--sp = (int)(pc + 1); pc = (int *)*pc; }        // jump to subroutine
    else if (i == BZ)  pc = a ? pc + 1 : (int *)*pc;                      // branch if zero
    else if (i == BNZ) pc = a ? (int *)*pc : pc + 1;                      // branch if not zero
    else if (i == ENT) { *--sp = (int)bp; bp = sp; sp = sp - *pc++; }     // enter subroutine
    else if (i == ADJ) sp = sp + *pc++;                                   // stack adjust
    else if (i == LEV) { sp = bp; bp = (int *)*sp++; pc = (int *)*sp++; } // leave subroutine
    else if (i == LI)  a = *(int *)a;                                     // load int
    else if (i == LC)  a = *(char *)a;                                    // load char
    else if (i == SI)  *(int *)*sp++ = a;                                 // store int
    else if (i == SC)  a = *(char *)*sp++ = a;                            // store char
    else if (i == PSH) *--sp = a;                                         // push

    //perform bitwise OR (|)
    else if (i == OR)  a = *sp++ |  a;

    //perform bitwise XOR (^)
    else if (i == XOR) a = *sp++ ^  a;

    //perform bitwise AND (&)
    else if (i == AND) a = *sp++ &  a;

    //perform equality check (==)
    else if (i == EQ)  a = *sp++ == a;

    //perform inequality check (!=)
    else if (i == NE)  a = *sp++ != a;

    //perform less than (<) comparison
    else if (i == LT)  a = *sp++ <  a;

    //perform greater than (>) comparison
    else if (i == GT)  a = *sp++ >  a;

    //perform less than or equal (<=) comparison
    else if (i == LE)  a = *sp++ <= a;

    //perform greater than or equal (>=) comparison
    else if (i == GE)  a = *sp++ >= a;

    //perform shift left (<<)
    else if (i == SHL) a = *sp++ << a;

    //perform shift right (>>)
    else if (i == SHR) a = *sp++ >> a;

    //perform addition (+)
    else if (i == ADD) a = *sp++ +  a;

    //perform subtraction (-)
    else if (i == SUB) a = *sp++ -  a;

    //perform multiplication (*)
    else if (i == MUL) a = *sp++ *  a;

    //perform division (/)
    else if (i == DIV) a = *sp++ /  a;

    //perform modulus (%)
    else if (i == MOD) a = *sp++ %  a;

    //open a file (system call: open)
    else if (i == OPEN) a = open((char *)sp[1], *sp);

    //read from a file descriptor (system call: read)
    else if (i == READ) a = read(sp[2], (char *)sp[1], *sp);

    //close a file descriptor (system call: close)
    else if (i == CLOS) a = close(*sp);

    //handle printf function (system call: printf)
    else if (i == PRTF) { 
        t = sp + pc[1];  
        a = printf((char *)t[-1], t[-2], t[-3], t[-4], t[-5], t[-6]);  
    }

    //allocate memory (system call: malloc)
    else if (i == MALC) a = (int)malloc(*sp);

    //free allocated memory (system call: free)
    else if (i == FREE) free((void *)*sp);

    //set memory (system call: memset)
    else if (i == MSET) a = (int)memset((char *)sp[2], sp[1], *sp);

    //compare memory blocks (system call: memcmp)
    else if (i == MCMP) a = memcmp((char *)sp[2], (char *)sp[1], *sp);

    if (i == EXIT) { printf("exit(%d) cycle = %d\n", *sp, cycle); return *sp; }  //exit program
    else { printf("unknown instruction = %d! cycle = %d\n", i, cycle); return -1; }  //error
  }
}