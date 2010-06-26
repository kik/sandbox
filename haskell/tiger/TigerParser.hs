module TigerParser where
import Parsec
import qualified Text.ParserCombinators.Parsec.Token as P
import Text.ParserCombinators.Parsec.Language
import Text.ParserCombinators.Parsec.Expr

run :: (Show a) => GenParser tok () a -> [tok] -> IO ()
run = parseTest

lexer :: P.TokenParser ()
lexer = P.makeTokenParser (haskellDef
                           { reservedNames = rn,
                             reservedOpNames = ro })
      where
        rn = words "while for to break let in end function var type array if then else do of nil"
        ro = map (:[]) ",:;()[]{}.+-*/=<>&|" ++ ["<>", "<=", ">=", ":="]


whiteSpace= P.whiteSpace lexer
lexeme    = P.lexeme lexer
symbol    = P.symbol lexer
natural   = P.natural lexer
parens    = P.parens lexer
semi      = P.semi lexer
identifier= P.identifier lexer
reserved  = P.reserved lexer
reservedOp= P.reservedOp lexer
stringLiteral = P.stringLiteral lexer

op = reservedOp

idt = symbol

{-
lvalue :: Parser ()
lvalue =  idt
      <|> (lvalue >> reservedOp "." >> idt)
      <|> (lvalue >> reservedOp "[" >> expr >> "]")
-}

type Symbol = String

data Var = SimpleVar Symbol
         | FieldVar Var Symbol
         | SubscriptVar Var Exp
         deriving Show

data Exp = VarExp Var
         | NilExp
         | IntExp Integer
         | StringExp String
         | CallExp { func :: Symbol, args :: [Exp] }
         | OpExp { left :: Exp, oper :: Oper, right :: Exp }
         | RecordExp { fields :: [(Symbol, Exp)], typ :: Symbol }
         | SeqExp [Exp]
         | AssignExp { var :: Var, exp :: Exp }
         | IfExp { test :: Exp,  then' :: Exp, else' :: (Maybe Exp) }
         | WhileExp { test :: Exp, body :: Exp }
         | ForExp { forVar :: Symbol, escape :: Bool, lo :: Exp, hi :: Exp, body :: Exp }
         | BreakExp
         | LetExp { decs :: [Dec], body :: Exp }
         | ArrayExp { typ :: Symbol, size :: Exp, ini :: Exp }
         deriving Show

data Dec = FunctionDec [FunDec]
         | VarDec { name :: Symbol, decEscape :: Bool, varType :: Maybe Symbol, varInit :: Exp }
         | TypeDec [(Symbol, Ty)]
         deriving Show

data Ty = NameTy Symbol
        | RecordTy [Field]
        | ArrayTy Symbol
           deriving Show
        
data Oper = PlusOp | MinusOp | TiemsOp | DivideOp
          | EqOp | NeqOp | LtOp | LeOp | GtOp | GeOp
         deriving Show

data Field = Field { fieldName :: Symbol, fieldEscape :: Bool, fieldType :: Symbol }
           deriving Show
data FunDec = FunDec { funDecName :: Symbol, params :: [Field], result :: Maybe Symbol, funDecBody :: Exp }
           deriving Show

optionMayBe :: Parser a -> Parser (Maybe a)
optionMayBe x = option Nothing $ Just <$> x

sepBy2 :: Parser a -> Parser sep -> Parser [a]
x `sepBy2` sep = (:) <$> x <* sep <*> x `sepBy1` sep

{--

  t = hd
    | t tls
  
  --}
chainPostfix :: Parser a -> Parser (a -> a) -> Parser a
chainPostfix hd tls = foldl (flip ($)) <$> hd <*> many tls

lvalue :: Parser Var
lvalue = (SimpleVar <$> identifier) `chainPostfix` (flip FieldVar <$ op "." <*> identifier
                                                     <|> flip SubscriptVar <$ op "[" <*> expr <* op "[")

expr :: Parser Exp
expr =  try (CallExp <$> identifier <* op "(" <*> expr `sepBy` op "," <* op ")")
    <|> VarExp <$> lvalue
    <|> NilExp <$  kw_nil
    <|> IntExp <$> natural
    <|> StringExp <$> stringLiteral
    <|> IfExp  <$> (kw_if >> expr)
               <*> (kw_then >> expr)
               <*> optionMayBe (kw_else >> expr)
    <|> SeqExp <$ op "(" <*> expr `sepBy2` op ";" <* op ")"
  where
    kw_nil  = reserved "nil"
    kw_if   = reserved "if"
    kw_then = reserved "then"
    kw_else = reserved "else"

program :: Parser Exp
program = expr <* eof

{-
expr :: Parser Integer
expr  = buildExpressionParser table factor <?> "expression"

table = [[op "*" (*) AssocLeft, op "/" div AssocLeft],
         [op "+" (+) AssocLeft, op "-" (-) AssocLeft]]
      where
        op s f assoc = Infix (do { reservedOp s; return f} <?> "operator") assoc

factor = P.parens lexer expr <|> P.natural lexer
-}

