structure Parse :> PARSE =
struct 
  structure HarmlessLrVals = HarmlessLrValsFun(structure Token = LrParser.Token)
  structure HarmlessLex = HarmlessLexFun(structure Tokens = HarmlessLrVals.Tokens)
  structure HarmlessParser = Join(structure ParserData = HarmlessLrVals.ParserData
			structure Lex=HarmlessLex
			structure LrParser = LrParser)
  fun parse filename =
      let val _ = (ErrorMsg.reset(); ErrorMsg.fileName := filename)
	  val file = TextIO.openIn filename
	  fun get _ = TextIO.input file
	  fun parseerror(s,p1,p2) = ErrorMsg.error (p1,p2) s
	  val lexer = LrParser.Stream.streamify (HarmlessLex.makeLexer get)
	  val (absyn, _) = HarmlessParser.parse(30,lexer,parseerror,())
       in TextIO.closeIn file;
	   absyn
      end handle LrParser.ParseError => raise ErrorMsg.Error


 end



