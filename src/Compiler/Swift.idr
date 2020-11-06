module Compiler.Swift

import Compiler.Common
import Compiler.CompileExpr
import Compiler.LambdaLift
import Compiler.ANF
import Compiler.Inline

import Core.Context
import Core.Context.Log
import Core.Directory
import Core.Name
import Core.Options
import Core.TT

import Data.IORef
import Data.List
import Data.List1
import Data.NameMap
import Data.Nat
import Data.Strings
import Data.Vect

import System
import System.Info
import System.File

import Idris.Version
import Utils.Hex
import Utils.Path

IdrisFunctionName : Type
IdrisFunctionName = String

data SwiftFunctionName = SwiftFnName String

||| There are a few operator/function names from Idris
||| that have hardcoded Swift alternatives.
hardcodedFnNames : List (String, String)
hardcodedFnNames = [
  (">>=", "bind"),
  ("<*>", "apply"),
  ("<$>", "map")
]

swiftTypeOfCFType : CFType -> Core String
swiftTypeOfCFType CFUnit          = pure $ "Void"
swiftTypeOfCFType CFInt           = pure $ "Int"
swiftTypeOfCFType CFUnsigned8     = pure $ "UInt8"
swiftTypeOfCFType CFUnsigned16    = pure $ "UInt16"
swiftTypeOfCFType CFUnsigned32    = pure $ "UInt32"
swiftTypeOfCFType CFUnsigned64    = pure $ "UInt64"
swiftTypeOfCFType CFString        = pure $ "String"
swiftTypeOfCFType CFDouble        = pure $ "Double"
swiftTypeOfCFType CFChar          = pure $ "Char"
swiftTypeOfCFType CFPtr           = pure $ "CFPtr"
swiftTypeOfCFType CFGCPtr         = pure $ "CFGCPtr"
swiftTypeOfCFType CFBuffer        = pure $ "CFBuffer"
swiftTypeOfCFType CFWorld         = pure $ "CFWorld"
swiftTypeOfCFType (CFFun x y)     = pure $ "CFFun"
swiftTypeOfCFType (CFIORes x)     = pure $ "CFIORes"
swiftTypeOfCFType (CFStruct x ys) = pure $ "CFStruct"
swiftTypeOfCFType (CFUser x ys)   = pure $ "CFUser"

swiftTypeOfTypeConstant : Constant -> Core $ Maybe String
swiftTypeOfTypeConstant IntType     = pure $ Just "Int"
swiftTypeOfTypeConstant IntegerType = pure $ Just "Int"
swiftTypeOfTypeConstant Bits8Type   = pure $ Just "UInt8"
swiftTypeOfTypeConstant Bits16Type  = pure $ Just "UInt16"
swiftTypeOfTypeConstant Bits32Type  = pure $ Just "UInt32"
swiftTypeOfTypeConstant Bits64Type  = pure $ Just "UInt64"
swiftTypeOfTypeConstant StringType  = pure $ Just "String"
swiftTypeOfTypeConstant CharType    = pure $ Just "Char"
swiftTypeOfTypeConstant DoubleType  = pure $ Just "Double"
swiftTypeOfTypeConstant WorldType   = pure $ Just "World"
swiftTypeOfTypeConstant _ = pure $ Nothing

replaceHardcodedNames : List Char -> List Char
replaceHardcodedNames n = foldr replaceName n hardcodedFnNames
  where
    replaceWithin : (find : List Char) -> (replace : List Char) -> (target : List Char) -> List Char
    replaceWithin find replace [] = []
    replaceWithin find replace target@(c :: cs) = if (isPrefixOf find target)
                                                    then replace ++ replaceWithin find replace (drop (length find) target)
                                                    else c :: (replaceWithin find replace cs)

    replaceName : (String, String) -> List Char -> List Char
    replaceName (find, replace) target = replaceWithin (unpack find) (unpack replace) target

isOperatorSpecialChar : Char -> Bool
isOperatorSpecialChar = flip any specialChars . (flip apply)
  where
    isElem : List Char -> Char -> Bool
    isElem = flip elem 

    charBetween : (lower : Char) -> (upper : Char) -> Char -> Bool
    charBetween lower upper c = c >= lower && c <= upper

    ||| Special characters taken directly from Swift reference
    ||| https://docs.swift.org/swift-book/ReferenceManual/zzSummaryOfTheGrammar.html
    specialChars : List (Char -> Bool)
    specialChars = [
      isElem ['/', '=', '-', '+', '!', '*', '%', '<', '>', '&', '|', '^', '~', '?'],
      isElem (chr <$> [0x00A1, 0x00A2, 0x00A3, 0x00A4, 0x00A5, 0x00A6, 0x00A7]),
      isElem (chr <$> [0x00A9, 0x00AB, 0x00AC, 0x00AE]),
      isElem (chr <$> [0x00B0, 0x00B1, 0x00B6, 0x00BB, 0x00BF, 0x00D7, 0x00F7]),
      isElem (chr <$> [0x2016, 0x2017, 0x2020, 0x2021, 0x2022, 0x2023, 0x2024, 0x2025, 0x2026, 0x2027, 0x3030]),
      charBetween '‰' '‾',          -- 0x2030 - 0x203E
      charBetween '⁁' '⁓',          -- 0x2041 - 0x2053
      charBetween '⁕' '⁞',          -- 0x2055 - 0x205E
      charBetween '←' (chr 0x23FF), -- 0x2190 - 0x23FF
      charBetween '─' '❵',          -- 0x2500 - 0x2755
      charBetween '➔' (chr 0x2BFF), -- 0x2794 – 0x2BFF
      charBetween '⸀' (chr 0x2E7F), -- 0x2E00 – 0x2E7F
      charBetween '、' '〃',        -- 0x3001 – 0x3003
      charBetween '〈' '〠'         -- 0x3008 – 0x3020
    ]

||| apply any escaping needed to turn an Idris function name
||| into a valid Swift function name
swiftFnName : IdrisFunctionName -> SwiftFunctionName
swiftFnName = wrap . addOpPrefix . replaceDescriptiveChars . replaceHardcodedNames . unpack
  where
    wrap : List Char -> SwiftFunctionName
    wrap = SwiftFnName . pack

    replaceDescriptiveChar : Char -> Char
    replaceDescriptiveChar ' ' = '_'
    replaceDescriptiveChar c = c

    replaceDescriptiveChars : List Char -> List Char
    replaceDescriptiveChars [] = []
    replaceDescriptiveChars (c :: cs) = replaceDescriptiveChar c :: replaceDescriptiveChars cs

    addOpPrefix : List Char -> List Char
    addOpPrefix []       = []
    addOpPrefix n@(c :: _) = if (isOperatorSpecialChar c)
                             then 'o' :: 'p' :: '_':: n
                             else n

SwiftFnTypes : Type
SwiftFnTypes = List (Maybe String)

typeForName : { auto ctx : Context } -> Name -> Core $ ClosedTerm
typeForName n = do Just type <- lookupTyExact n ctx
                     | Nothing => throw $ InternalError $ "Can't find type for " ++ (show n)
                   pure type

fnTypeFromBoundTerm :  { auto ctx : Context }
                    -> { vars : _ } 
                    -> Term vars 
                    -> Core $ List (Maybe String)
fnTypeFromBoundTerm (Bind fc x b scope) = pure $ (Just $ show $ !(full ctx $ binderType b)) :: !(fnTypeFromBoundTerm scope)
fnTypeFromBoundTerm (PrimVal fc c) = pure $ [!(swiftTypeOfTypeConstant c)]
fnTypeFromBoundTerm (Ref fc nt n) = pure $ [Just $ show !(full ctx n)]
fnTypeFromBoundTerm (Meta _ _ _ _) = pure [Just "meta"]
fnTypeFromBoundTerm (Local _ _ _ _) = pure [Just "local"]
fnTypeFromBoundTerm (App _ _ _) = pure [Just "app"]
fnTypeFromBoundTerm (Erased _ _) = pure [Just "erased"]
fnTypeFromBoundTerm other = throw $ InternalError $ "Attempting to get bound term type from non-bind term." ++ (show other)

fnTypeFromName :  { auto ctx : Context }
               -> Name
               -> Core $ List (Maybe String)
fnTypeFromName n = fnTypeFromBoundTerm !(typeForName n)

record SwiftDef where
  constructor MkSwiftDef
  def  : NamedDef
  type : SwiftFnTypes

record NamespacedName where
  constructor MkNamespacedName
  path : List String -- unlike Namespace, stored in forward order.
  name : String

namespacedDef : Context -> (Name, FC, NamedDef) -> Core (NamespacedName, FC, SwiftDef)
namespacedDef ctx (n, fc, nd) = pure $ (expandNS n, fc, MkSwiftDef nd !(fnTypeFromName n)) where
  expandNS : Name -> NamespacedName
  expandNS (NS ns n) = record { path $= (reverse $ unsafeUnfoldNamespace ns ++) } (expandNS n)
  expandNS (UN str) = MkNamespacedName [] str
  expandNS (MN str int) = MkNamespacedName [] ("_" ++ str ++ "_" ++ (show int))
  expandNS (PV n _) = expandNS n -- TODO: handle differently?
  expandNS (DN _ n) = expandNS n -- TODO: handle differently?
  expandNS (RF str) = MkNamespacedName [] str
  expandNS (Nested i n) = record { name $= ("_nest" ++ (show i) ++) } (expandNS n)
  expandNS (CaseBlock str i) = MkNamespacedName [] ("case_" ++ str ++ "_" ++ (show i))
  expandNS (WithBlock str i) = MkNamespacedName [] ("with_" ++ str ++ "_" ++ (show i))
  expandNS (Resolved i) = MkNamespacedName [] ("fn_" ++ (show i))

||| Consume one path component of a namespaced name, producing either
||| the eventual name or the next namespace component and the remaining
||| NamespacedName.
consumeNameComponent : NamespacedName -> Either String (String, NamespacedName)
consumeNameComponent (MkNamespacedName [] name) = Left name
consumeNameComponent (MkNamespacedName (x :: xs) name) = Right (x, MkNamespacedName xs name)

indentation : (quantity : Nat) -> String
indentation quantity = pack $ replicate quantity ' '

indentAmount : Nat
indentAmount = 2

||| Indent the given text block (which may contain newlines) by the
||| indicated amount.
|||
||| The indent amount is the number of times to indent the block, not
||| the total number of spaces to indent by. So, 2 == (2 * indentAmount).
indentBlock : { default 1 indent : Nat } -> (textBlock : String) -> String
indentBlock {indent} = recombine . toList . (split (== '\n'))
  where
    spaces : String
    spaces = indentation $ indent * indentAmount

    recombine : List String -> String
    recombine = (spaces ++) . concat . (intersperse $ "\n" ++ spaces)

swiftTodo : Core String
swiftTodo = pure "// TODO: "

getExprImp : NamedCExp -> Core String
getExprImp orig@(NmLocal fc n) = pure $ !swiftTodo ++ (show orig)
getExprImp orig@(NmRef fc x) = pure $ !swiftTodo ++ (show orig)
getExprImp orig@(NmLam fc x y) = pure $ !swiftTodo ++ (show orig)
getExprImp orig@(NmLet fc x y z) = pure $ !swiftTodo ++ (show orig)
getExprImp orig@(NmApp fc x xs) = pure $ !swiftTodo ++ (show orig)
getExprImp orig@(NmCon fc x tag xs) = pure $ !swiftTodo ++ (show orig)
getExprImp orig@(NmOp fc x xs) = pure $ !swiftTodo ++ (show orig)
getExprImp orig@(NmExtPrim fc p xs) = pure $ !swiftTodo ++ (show orig)
getExprImp orig@(NmForce fc x) = pure $ !swiftTodo ++ (show orig)
getExprImp orig@(NmDelay fc x) = pure $ !swiftTodo ++ (show orig)
getExprImp orig@(NmConCase fc sc xs x) = pure $ !swiftTodo ++ (show orig)
getExprImp orig@(NmConstCase fc sc xs x) = pure $ !swiftTodo ++ (show orig)
getExprImp orig@(NmPrimVal fc x) = pure $ !swiftTodo ++ (show orig)
getExprImp orig@(NmErased fc) = pure $ !swiftTodo ++ (show orig)
getExprImp orig@(NmCrash fc x) = pure $ !swiftTodo ++ (show orig)

||| A function definition already assumed to be
||| nested within any relevant namespaces.
record LeafDef where
  constructor MkLeafDef
  name : IdrisFunctionName
  fc   : FC
  def  : SwiftDef

data FFI = FgnC | FgnNode | FgnSwift

Show FFI where
  show FgnC = "C"
  show FgnNode = "node"
  show FgnSwift = "swift"

Eq FFI where
  (==) FgnC FgnC         = True
  (==) FgnNode FgnNode   = True
  (==) FgnSwift FgnSwift = True
  (==) _ _               = False

ffiFromStr : String -> Maybe FFI
ffiFromStr s = case s of
                    "C"     => Just FgnC
                    "node"  => Just FgnNode
                    "swift" => Just FgnSwift
                    _       => Nothing

record ForeignInv where
  constructor FInv
  ffi : FFI
  args : List String

||| C-style foreign invocations are formatted as
||| "C:funcName, libName"
|||
||| This function teases that all apart.
foreignInvs : List String -> List ForeignInv
foreignInvs xs = catMaybes $ foreignInv <$> xs where
  foreignInv : String -> Maybe ForeignInv
  foreignInv s = let (ffiStr ::: rest) = split (== ':') s
                     args              = trim <$> (split (== ',') $ concat rest)
                 in do ffi <- ffiFromStr ffiStr 
                       pure $ FInv ffi $ toList args 

data ExternalLibs : Type where

addExternalLib : {auto e : Ref ExternalLibs (List String)}
               -> String
               -> Core ()
addExternalLib extLib = do
    libs <- get ExternalLibs
    case elem extLib libs of
        True  => pure () -- library already in list
        False => do
            put ExternalLibs (extLib :: libs)

||| Not all types get propogated down to the c FFI.
||| Types that don't will return Nothing.
cFFITypeOfCFType :  CFType 
                 -> Core $ Maybe String
cFFITypeOfCFType CFWorld = pure $ Nothing
cFFITypeOfCFType x       = pure $ Just !(swiftTypeOfCFType x)

argNamesFromList :  { 0 ty : Type } 
                 -> List ty 
                 -> Nat 
                 -> Core (List String)
argNamesFromList [] _ = pure []
argNamesFromList (x :: xs) k = pure $ ("arg_" ++ show k) :: !(argNamesFromList xs (S k))

record FunctionArgument where
  constructor FnArgument
  typeName, argName : String
  cfType : CFType

ffiArgList :  List CFType
           -> Core $ List FunctionArgument
ffiArgList cftypeList = 
  do typeNameList <- traverse cFFITypeOfCFType cftypeList
     varList      <- argNamesFromList cftypeList 1
     let triples = zip3 typeNameList varList cftypeList
     let nonNulls = catMaybes $ liftNulls <$> triples
     pure $ (\(x,y,z) => FnArgument x y z) <$> nonNulls
    where
      liftNulls : (Maybe String, String, CFType) -> Maybe (String, String, CFType)
      liftNulls (Just t, n, cft) = Just (t, n, cft)
      liftNulls (Nothing, _, _) = Nothing

idrisArgList :  (types : SwiftFnTypes)
             -> List Name
             -> Core $ List FunctionArgument
idrisArgList types argNames = 
  do varList <- pure $ show <$> argNames
     let triples = zip3 types varList ((const CFString) <$> argNames)
     let nonNulls = catMaybes $ liftNulls <$> triples
     pure $ (\(x,y,z) => FnArgument x y CFString) <$> nonNulls
    where
      liftNulls : (Maybe String, String, CFType) -> Maybe (String, String, CFType)
      liftNulls (Just t, n, cft) = Just (t, n, cft)
      liftNulls (Nothing, _, _) = Nothing

||| Given the results of ffiArgList, produce the invocation argument list.
||| Invoking a la Swift without argument names (so just a comma separated list
||| of argument names).
cInvArgList : List FunctionArgument -> Core String
cInvArgList args = pure $ concat $ intersperse ", " $ takeName <$> args where
  takeName : FunctionArgument -> String
  takeName (FnArgument _ name _) = name

stringArgs : List FunctionArgument -> List String
stringArgs args = (\(FnArgument _ n _) => n) <$> filter isString args where
  isString : FunctionArgument -> Bool
  isString (FnArgument _ _ CFString) = True
  isString (FnArgument _ _ _)        = False

||| A Swift String must be wrapped in an unsafe pointer closure to be passed
||| to a C function as char *.
wrapStringForCChar :  (varname : String) 
                   -> (body : String) 
                   -> String
wrapStringForCChar varname body = varname ++ ".withCString { immutable_" ++ varname ++ " in \n"
                               ++ indentBlock ( 
                                    "let " ++ varname ++ " = UnsafeMutablePointer(mutating: immutable_" ++ varname ++ ")\n"
                                  ++ body
                                  )
                               ++ "\n}"

||| The C invocation is built from both FFI args (i.e. the things from the Idris 2
||| %foreign definition) and function args (the actual arguments passed on to the
||| C function being called.
getCInv :  { auto e : Ref ExternalLibs (List String) }
        -> (funcArgs : List CFType)
        -> (ret : CFType)
        -> (ffiArgs : List String) 
        -> Core String
getCInv _ _ [] = throw $ InternalError "C foreign function invocations are expected to have at least one argument."
getCInv funcArgs ret (cname :: xs) = 
  do case (head' xs) of 
       (Just libName) => addExternalLib libName
       Nothing => pure ()
     argList <- ffiArgList funcArgs
     invocation <- pure $ cname ++ "(" ++ !(cInvArgList argList) ++ ")" 
     wrappedInvocation <- pure $ foldr wrapStringForCChar invocation $ stringArgs argList
     pure $ wrappedInvocation

getForeignFnApp :  { auto e : Ref ExternalLibs (List String) }
                -> (fname : String) 
                -> (funcArgs : List CFType)
                -> (ret : CFType)
                -> List ForeignInv 
                -> Core String
-- for now, only handle C foreign invocations
getForeignFnApp fname funcArgs ret xs = case (find (\i => i.ffi == FgnC) xs) of
                                          Just inv => getCInv funcArgs ret inv.args 
                                          Nothing => pure $ "/* non-c FFI */"
                        --     Nothing => throw $ 
                        --                  InternalError $ "Only supports C foreign functions currently. Found [" 
                        --                               ++ (concat $ show . (.ffi) <$> xs) 
                        --                               ++ "] for foreign function named " ++ fname

||| Given the results of ffiArgList, produce the definition argument list.
||| Argument list a la Swift without argument names.
defArgList : List FunctionArgument -> Core String
defArgList args = pure $ concat $ intersperse ", " $ takeNameAndType <$> args where
  takeNameAndType : FunctionArgument -> String
  takeNameAndType (FnArgument type name _) = "_ " ++ name ++ ": " ++ type

staticAnnot : (global : Bool) -> String
staticAnnot global = if global then "" else "static "

getForeignFnImp :  { auto e : Ref ExternalLibs (List String) }
                -> (global : Bool) -- if true, expected to be globally scoped
                -> (name : SwiftFunctionName) 
                -> (args : List CFType) 
                -> (ret : CFType) 
                -> (invocations : List ForeignInv) 
                -> Core String
getForeignFnImp global (SwiftFnName name) args ret invocations = 
  pure $ (staticAnnot global) ++ "func " ++ name ++ "(" ++ !(defArgList !(ffiArgList args)) ++ ") {\n"
      ++ indentBlock !(getForeignFnApp name args ret invocations) 
      ++ "\n}"

getFnImp :  (global : Bool) -- if true, function is scoped globally
         -> (name : SwiftFunctionName)
         -> (types : SwiftFnTypes)
         -> (argNames : List Name)
         -> (exp : NamedCExp)
         -> Core String
getFnImp global (SwiftFnName name) types argNames exp = 
  pure $ (staticAnnot global) ++ "func " ++ name ++ "(" ++ !(defArgList !(idrisArgList types argNames)) ++ ") {\n"
      ++ indentBlock ("// " ++ show types)
      ++ indentBlock !(getExprImp exp)
      ++ "\n}"

||| Given a function name, file context, and defintion,
||| produce a Swift implementation.
|||
||| The name is assumed fully localized to whatever enum
||| scope the function will be defined within.
getImp :  { auto e : Ref ExternalLibs (List String) }
       -> { default 0 indent : Nat } 
       -> (global : Bool) -- if true, expected to be globally scoped
       -> LeafDef 
       -> Core String 
getImp global (MkLeafDef name fc (MkSwiftDef def type)) = getImp' name fc type def 
  where
    getImp' : (name: String) -> FC -> (types : SwiftFnTypes) -> (def : NamedDef) ->  Core String
    getImp' name fc types (MkNmFun args exp) =
      pure $ indentBlock {indent} !(getFnImp global (swiftFnName name) types args exp)

    getImp' name fc types (MkNmError exp) =
      throw $ (InternalError $ show exp)

    getImp' name fc types (MkNmForeign cs args ret) =
      pure $ indentBlock {indent} !(getForeignFnImp global (swiftFnName name) args ret (foreignInvs cs))

    getImp' name fc types (MkNmCon tag arity nt) =
      pure $ indentBlock {indent}
             !swiftTodo 
          ++ "cns " ++ name ++ (show tag) ++ " arity: " ++ (show arity) ++ " nt: " ++ (show nt)

||| A hierarchy of function definitions
||| by namespace.
record NestedDefs where
  constructor MkNestedDefs
  children : List (String, NestedDefs)
  defs     : List LeafDef

initNestedDefs : NestedDefs
initNestedDefs = MkNestedDefs [] []

mutual
  ||| Get all implementations for things in the current scope.
  ||| In the Swift backend, things are scoped with enums that
  ||| work to create both module and namespace scopes.
  getScopeImps :  { auto e : Ref ExternalLibs (List String) } 
               -> (global : Bool) -- true if the scope is global (only the root scope is).
               -> NestedDefs 
               -> Core String
  getScopeImps global ndefs = 
    do fnImps       <- traverse id $ (getImp global) <$> ndefs.defs
       childrenImps <- traverse id $  getEnumImp     <$> ndefs.children

       pure $ concatDefs fnImps ++ concat childrenImps where
         concatDefs : List String -> String
         concatDefs = (foldr (\s => (s ++ "\n" ++)) "") 

  getEnumImp :  { auto e : Ref ExternalLibs (List String) }
             -> (String, NestedDefs) 
             -> Core String
  getEnumImp (name, ndefs) = do defs <- getScopeImps False ndefs
                                pure $ indentBlock $ header name ++ (indentBlock defs) ++ footer
    where
      header : String -> String
      header name = "\n" ++ "enum " ++ name ++ " {\n"

      footer : String
      footer = "\n}"

replaceValueOnKey : Eq k => (key : k) -> (replacement: a) -> List (k, a) -> List (k, a)
replaceValueOnKey key replacement xs = map (\(k, v) => if k == key then (k, replacement) else (k, v)) xs

mutual
  storeChildDef : (key : String) 
                -> (NamespacedName, FC, SwiftDef) 
                -> List (String, NestedDefs) 
                -> List (String, NestedDefs)
  storeChildDef key def children = 
    case (lookup key children) of
      Nothing   => (key, storeDef def initNestedDefs) :: children
      (Just nd) => replaceValueOnKey key (storeDef def nd) children

  storeDef : (NamespacedName, FC, SwiftDef) -> NestedDefs -> NestedDefs
  storeDef (nsn, fc, sd) acc = 
    case (consumeNameComponent nsn) of
      (Left name)          => record { defs $= ((MkLeafDef name fc sd) ::) } acc
      (Right (path, rest)) => record { children $= (storeChildDef path (rest, fc, sd)) } acc

||| Group all function definitions by namespace
||| in a nested fashion so that we can export the
||| swift definitions in nested enums.
namespacedDefs : Context -> List (Name, FC, NamedDef) -> Core NestedDefs
namespacedDefs ctx defs = do nds <- traverse id $ namespacedDef ctx <$> defs
                             pure (foldr storeDef initNestedDefs nds) 

capitalized : String -> String
capitalized x = pack $ capitalFirst (unpack x) where
  capitalFirst : List Char -> List Char
  capitalFirst [] = []
  capitalFirst (x :: xs) = (toUpper x) :: xs

underscored : String -> String
underscored = pack . (replaceOn '-' '_') . unpack

||| takes a library name and creates a valid name for a
||| Swift module.
moduleName : (libName : String) -> String
moduleName = capitalized . underscored

||| Takes a library name and returns the linker name.
||| For example, "libidris2_support" because "idris2_supprt"
linkerName : (libName : String) -> String
linkerName libName = lname $ unpack libName where
  lname : List Char -> String
  lname ('l' :: 'i' :: 'b' :: name) = pack name
  lname name = pack name

||| Get the "import" lines that are needed at
||| the top of the main.swift file.
getImports : (libNames : List String) -> Core String
getImports libNames = pure $ concat $ intersperse "\n" $ ("import " ++) . moduleName <$> libNames

||| Compile a TT expression to Swift
compileToSwift :  { auto e : Ref ExternalLibs (List String) }
               -> Ref Ctxt Defs 
               -> Term [] 
               -> Core String
compileToSwift c tm = do cdata <- getCompileData Cases tm
                         defs <- get Ctxt
                         ndefs <- namespacedDefs defs.gamma cdata.namedDefs 
                         --
                         let ctx = defs.gamma
                         allns <- allNames ctx
                         case (head' allns) of
                              Just n => do tmp <- typeForName n 
                                           tyNames <- fnTypeFromBoundTerm tmp
                                           log "swft" 1 $ (show n) ++ "   " ++ (show tyNames)
                              Nothing => pure ()
                         --
                         imps <- getScopeImps True ndefs
                         libs <- get ExternalLibs
                         imports <- getImports libs
                         pure $ imports ++ "\n\n"
                             ++ imps ++ "\n\n"
                             ++ "func main() {}\n"

||| The frontend is a wrapper around the compiler and other
||| swift compiler utilities.
data SwiftExec = Interp | Compiler | Frontend

findSwift : SwiftExec -> IO String
findSwift Interp = pure "swift"
findSwift Compiler = pure "swiftc"
findSwift Frontend = pure "swift"

quoted : String -> String
quoted s = "\"" ++ s ++ "\""

packageExecProduct : (target : String) -> String
packageExecProduct target = ".executable(name: " ++ quoted target 
                         ++ ", targets: [" ++ (quoted $ moduleName target) 
                         ++ "])"

packageLibProduct : (libName : String) -> String
packageLibProduct libName = ".library(name: " ++ quoted libName ++ ", targets: [" 
                         ++ (quoted $ moduleName libName) 
                         ++ "])"

packageTarget : (target : String) -> (dependencies : List String) -> String
packageTarget target dependencies = ".target(name: " ++ (quoted $ moduleName target) ++ ", dependencies: [" 
                                 ++ (concat $ intersperse ", " (quoted . moduleName <$> dependencies)) ++ "])"

packageLibTarget : (libName : String) -> String
packageLibTarget libName = ".systemLibrary(name: " ++ (quoted $ moduleName libName) ++ ")"

getPackageManifest :  (externalLibs : List String) 
                   -> (target : String) 
                   -> Core String
getPackageManifest externalLibs target = 
  pure $ "// swift-tools-version:5.1\n\n"
      ++ "import PackageDescription \n\n"
      ++ "let package = Package(\nname: " ++ (quoted $ moduleName target) ++ ",\n"
      ++ "products: [\n" 
      ++ packageExecProduct target ++ ",\n"
      ++ (concat $ intersperse ", \n" $ packageLibProduct <$> externalLibs) 
      ++ "],\n"
      ++ "targets: [\n"
      ++ packageTarget target externalLibs ++ ",\n"
      ++ (concat $ intersperse ", \n" $ packageLibTarget <$> externalLibs)
      ++ "]\n)\n"

getLibModulemap :  (libName : String)
                -> Core String
getLibModulemap libName = 
  pure $ "module " ++ moduleName libName ++ " {\n"
      ++ "header " ++ quoted (".." </> ".." </> "Headers" </> "bridge_" ++ (moduleName libName) ++ ".h") ++ "\n"
      ++ "link " ++ (quoted $ linkerName libName) ++ "\n"
      ++ "export *"
      ++ "\n}"

writeLibModulemap :  (sourceDir : String)
                  -> (libName : String)
                  -> Core ()
writeLibModulemap sourceDir libName = 
  do let libSourceDir = sourceDir </> moduleName libName
     coreLift $ mkdirAll libSourceDir
     let modulemapOut = libSourceDir </> "module.modulemap"
     modulemap <- getLibModulemap libName
     Right () <- coreLift (writeFile modulemapOut modulemap)
       | Left err => throw (FileErr modulemapOut err)
     pure ()

builtinHeaderTranslation : (libName : String) -> String
builtinHeaderTranslation "libidris2_support" = "idris_support"
builtinHeaderTranslation libName = libName

getLibBridgeHeader :  (libName : String)
                   -> Core String
getLibBridgeHeader libName = pure $ "#include <" ++ builtinHeaderTranslation libName ++ ".h>\n"

writeLibBridgeHeader :  (headerDir : String)
                     -> (libName : String)
                     -> Core ()
writeLibBridgeHeader headerDir libName = 
  do let bridgeHeaderOut = headerDir </> "bridge_" ++ (moduleName libName) ++ ".h"
     bridgeHeader <- getLibBridgeHeader libName
     Right () <- coreLift (writeFile bridgeHeaderOut bridgeHeader)
       | Left err => throw (FileErr bridgeHeaderOut err)
     pure ()

swiftPrelude : Core String
swiftPrelude = pure $ "typealias CFWorld = String\n"

||| Swift implementation of the `compileExpr` interface.
compileExpr : Ref Ctxt Defs 
            -> (tmpDir : String) 
            -> (outputDir : String) 
            -> ClosedTerm 
            -> (outfile : String) 
            -> Core (Maybe String)
compileExpr c tmpDir outputDir tm outfile =
  do let sourceDir = outputDir </> "Sources"
     let headerDir = outputDir </> "Headers"
     let targetSourceDir = sourceDir </> moduleName outfile
     let execOut = targetSourceDir </> "main.swift"
     let manifestOut = outputDir </> "Package.swift"
     coreLift $ mkdirAll targetSourceDir
     coreLift $ mkdirAll headerDir
     
     newRef ExternalLibs []

     swift <- pure $ !swiftPrelude ++ !(compileToSwift c tm)
     externalLibs <- get ExternalLibs
     packageManifest <- getPackageManifest externalLibs outfile

     Right () <- coreLift (writeFile execOut swift)
        | Left err => throw (FileErr execOut err)
     Right () <- coreLift (writeFile manifestOut packageManifest)
        | Left err => throw (FileErr manifestOut err)
     traverse_ id $ (writeLibModulemap sourceDir) <$> externalLibs
     traverse_ id $ (writeLibBridgeHeader headerDir) <$> externalLibs

     swiftexec <- coreLift $ findSwift Frontend

     -- TODO: add in additional lib directories to search in below command.
     let compileCmd = "cd " ++ outputDir ++ " && " 
                   ++ swiftexec ++ " build"
                   ++ " -Xswiftc -I -Xswiftc $(idris2 --libdir)/include"
                   ++ " -Xlinker -L -Xlinker $(idris2 --libdir)/lib" 

     coreLift $ putStrLn compileCmd
     ok <- coreLift $ system compileCmd
     if ok == 0
        then pure (Just execOut)
        else pure Nothing

||| Swift implementation of the `executeExpr` interface.
executeExpr : Ref Ctxt Defs -> (tmpDir : String) -> ClosedTerm -> Core ()
executeExpr c tmpDir tm
    = do let outn = tmpDir </> "_tmp_swift" ++ ".swift"
     --    swift <- compileToSwift c tm
     --    Right () <- coreLift $ writeFile outn swift
     --       | Left err => throw (FileErr outn err)
     --    swiftexec <- coreLift $ findSwift Interp
     --    coreLift $ system (swiftexec ++ " " ++ outn)
         pure ()

export
codegenSwift : Codegen
codegenSwift = MkCG compileExpr executeExpr
