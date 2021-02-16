package wptool;

import beaver.Symbol;
import wptool.Parser.Terminals;

%%

%class Scanner
%extends beaver.Scanner
%function nextToken
%type Symbol
%yylexthrow Scanner.Exception

%eofval{
	return newToken(Terminals.EOF);
%eofval}

%line
%column

%{
    Symbol resolve(String name) {
          return newToken(Terminals.ID,   name);
    }
	Symbol resolvePrimeGamma(String name) {
		// TODO not a big fan of this
		return newToken(Terminals.PRIMEGAMMAID, name.substring(6, name.length() - 1));
	}
	Symbol resolvePrime(String name) {
		return newToken(Terminals.PRIMEID, name.substring(0, name.length() - 1));
	}
	Symbol resolveGamma(String name) {
		return newToken(Terminals.GAMMAID, name.substring(6));
	}
	Symbol newToken(short id)
	{
		return newToken(id, yytext());
	}

	Symbol newToken(short id, Object value)
	{
		return new Symbol(id, yyline + 1, yycolumn + 1, yylength(), value);
	}
%}

NL = \r|\n|\r\n
WS = {NL} | [ \t\f]

%%

<YYINITIAL> {

"//" .* {NL} {}
"#"  .* {NL} {}
"/*" [^*] ~"*/" | "/*" "*"+ "/" {}
{WS}+ {}

"("         { return newToken(Terminals.LPAREN);   }
")"         { return newToken(Terminals.RPAREN);   }
"["         { return newToken(Terminals.LBRACK);   }
"]"         { return newToken(Terminals.RBRACK);   }
"{"         { return newToken(Terminals.LBRACE);   }
"}"         { return newToken(Terminals.RBRACE);   }
//"++"        { return newToken(Terminals.INCR);     }
//"--"        { return newToken(Terminals.DECR);     }
"."         { return newToken(Terminals.DOT);      }
"!"         { return newToken(Terminals.BANG);     }
"=>"         { return newToken(Terminals.IMPLIES);     }
// "~"         { return newToken(Terminals.TILDE);    }
// "sizeof"    { return newToken(Terminals.SIZEOF);   }
"*"         { return newToken(Terminals.STAR);     }
"/"         { return newToken(Terminals.DIV);      }
"%"         { return newToken(Terminals.MOD);      }
"+"         { return newToken(Terminals.PLUS);     }
"-"         { return newToken(Terminals.MINUS);    }
//"<<"        { return newToken(Terminals.SHL);      }
//">>"        { return newToken(Terminals.SHR);      }
//">>>"        { return newToken(Terminals.ASHR);      }
"<"         { return newToken(Terminals.LT);       }
"<="        { return newToken(Terminals.LE);       }
">="        { return newToken(Terminals.GE);       }
">"         { return newToken(Terminals.GT);       }
"=="        { return newToken(Terminals.EQ);       }
"!="        { return newToken(Terminals.NEQ);      }
"&"         { return newToken(Terminals.AMP);      }
// "^"         { return newToken(Terminals.CARET);    }
// "|"         { return newToken(Terminals.PIPE);     }
"&&"        { return newToken(Terminals.AND);      }
"||"        { return newToken(Terminals.OR);       }
// "?"         { return newToken(Terminals.QUESTION); }
":"         { return newToken(Terminals.COLON);    }
"="         { return newToken(Terminals.ASG); }

","         { return newToken(Terminals.COMMA);    }
";"         { return newToken(Terminals.SEMICOLON);}

"CAS"       { return newToken(Terminals.CAS);     }

//"break"     { return newToken(Terminals.BREAK);    }
//"return"    { return newToken(Terminals.RETURN);   }
//"continue"  { return newToken(Terminals.CONTINUE); }
"do"        { return newToken(Terminals.DO);       }
"while"     { return newToken(Terminals.WHILE);    }
//"for"       { return newToken(Terminals.FOR);      }
"if"        { return newToken(Terminals.IF);       }
"else"      { return newToken(Terminals.ELSE);     }
"assert"      { return newToken(Terminals.ASSERT);     }

//"fence"     { return newToken(Terminals.FENCE);    }
//"cfence"     { return newToken(Terminals.CFENCE);    }
"_L"       { return newToken(Terminals.LPRED);      }
"_PT"       { return newToken(Terminals.PT);      }
"_invariant" {return newToken(Terminals.INVARIANT);}
"_Gamma" {return newToken(Terminals.GAMMA);}
"_Gamma_0" {return newToken(Terminals.GAMMA_0);}
"global var"      { return newToken(Terminals.GLOBALVAR);     }
"local var"      { return newToken(Terminals.LOCALVAR);     }
"_Rely" {return newToken(Terminals.RELY);}
"_Guar" {return newToken(Terminals.GUAR);}
"global array"    { return newToken(Terminals.GLOBALARRAY);     }
"local array"    { return newToken(Terminals.LOCALARRAY);     }
"global obj"    { return newToken(Terminals.GLOBALOBJ);     }
"_Fields"    { return newToken(Terminals.FIELDS);     }

"TRUE" { return newToken(Terminals.TRUE);    }
"FALSE" { return newToken(Terminals.FALSE);    }
// "FORALL" { return newToken(Terminals.FORALL);    }
"LOW"   { return newToken(Terminals.LOW);    }
"HIGH" { return newToken(Terminals.HIGH);    }

"->"        { return newToken(Terminals.MAPSTO);    }
Gamma_[a-zA-Z][a-zA-Z0-9]*[']    { return resolvePrimeGamma(yytext()); }
Gamma_[a-zA-Z][a-zA-Z0-9]*    { return resolveGamma(yytext()); }
[a-zA-Z_][a-zA-Z_0-9]*['] { return resolvePrime(yytext()); }

[a-zA-Z_][a-zA-Z_0-9]*
            { return resolve(yytext()); }

[0-9]+      { return newToken(Terminals.NUM, new Integer(yytext())); }

[^]         { throw new Scanner.Exception("unexpected character '" + yytext() + "'"); }

}



