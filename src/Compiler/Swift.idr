module Compiler.Swift

import Compiler.Common
import Compiler.CompileExpr
import Compiler.LambdaLift
import Compiler.ANF
import Compiler.Inline

import Core.Context
import Core.Directory
import Core.Name
import Core.Options
import Core.TT

import Data.IORef
import Data.List
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

record NamespacedName where
  constructor MkNamespacedName
  path : List String -- unlike Namespace, stored in forward order.
  name : String

namespacedDef : (Name, FC, NamedDef) -> (NamespacedName, FC, NamedDef)
namespacedDef (n, fc, nd) = (expandNS n, fc, nd) where
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

getExprImp : NamedCExp -> Core String
getExprImp (NmLocal fc x) = ?getExprImp_rhs_1
getExprImp (NmRef fc x) = ?getExprImp_rhs_2
getExprImp (NmLam fc x y) = ?getExprImp_rhs_3
getExprImp (NmLet fc x y z) = ?getExprImp_rhs_4
getExprImp (NmApp fc x xs) = ?getExprImp_rhs_5
getExprImp (NmCon fc x tag xs) = ?getExprImp_rhs_6
getExprImp (NmOp fc x xs) = ?getExprImp_rhs_7
getExprImp (NmExtPrim fc p xs) = ?getExprImp_rhs_8
getExprImp (NmForce fc x) = ?getExprImp_rhs_9
getExprImp (NmDelay fc x) = ?getExprImp_rhs_10
getExprImp (NmConCase fc sc xs x) = ?getExprImp_rhs_11
getExprImp (NmConstCase fc sc xs x) = ?getExprImp_rhs_12
getExprImp (NmPrimVal fc x) = ?getExprImp_rhs_13
getExprImp (NmErased fc) = ?getExprImp_rhs_14
getExprImp (NmCrash fc x) = ?getExprImp_rhs_15

||| A function definition already assumed to be
||| nested within any relevant namespaces.
record LeafDef where
  constructor MkLeafDef
  name : String
  fc : FC
  def : NamedDef

||| Given a function name, file context, and defintion,
||| produce a Swift implementation.
|||
||| The name is assumed fully localized to whatever enum
||| scope the function will be defined within.
getImp : {default 0 indent : Nat} -> LeafDef -> Core String 
getImp def = getImp {indent} (def.name, def.fc, def.def) where
  getImp : {indent : Nat} -> (String, FC, NamedDef) -> Core String
  getImp (name, fc, MkNmFun args exp) =
   pure $ indentation indent ++ "fn " ++ name -- map (\s => "fn " ++ s) $ prettyName n -- FunDecl fc n args !(impExp True exp)
  getImp (name, fc, MkNmError exp) =
    throw $ (InternalError $ show exp)
  getImp (name, fc, MkNmForeign cs args ret) =
    pure $ indentation indent ++ "fgn " ++ name -- map (\s => "fgn " ++ s) $ prettyName n -- ForeignDecl n cs
  getImp (name, fc, MkNmCon tag arity nt) =
    pure $ indentation indent ++ "cns " ++ name ++ (show tag) ++ " arity: " ++ (show arity) ++ " nt: " ++ (show nt) -- map (\s => "constructor " ++ s) $ prettyName n -- DoNothing

||| A hierarchy of function definitions
||| by namespace.
record NestedDefs where
  constructor MkNestedDefs
  children : List (String, NestedDefs)
  defs : List LeafDef

initNestedDefs : NestedDefs
initNestedDefs = MkNestedDefs [] []

mutual
  ||| Get all implementations for things in the current scope.
  ||| In the Swift backend, things are scoped with enums that
  ||| work to create both module and namespace scopes.
  getScopeImps : {default 0 indent : Nat } -> NestedDefs -> Core String
  getScopeImps ndefs = do fnImps <- traverse id $ getImp {indent} <$> ndefs.defs
                          childrenImps <- traverse id $ getEnumImp {indent} <$> ndefs.children
                          pure $ concatDefs fnImps ++ concat childrenImps where
                            concatDefs : List String -> String
                            concatDefs = (foldr (\s => (s ++ "\n" ++)) "") 

  getEnumImp : {default 0 indent : Nat} -> (String, NestedDefs) -> Core String
  getEnumImp (name, ndefs) = do defs <- getScopeImps {indent=(indent + 4)} ndefs
                                pure $ header name ++ defs ++ footer where
                                  header : String -> String
                                  header name = "\n" ++ indentation indent ++ "enum " ++ name ++ " {\n"

                                  footer : String
                                  footer = "\n" ++ indentation indent ++ "}"

replaceValueOnKey : Eq k => (key : k) -> (replacement: a) -> List (k, a) -> List (k, a)
replaceValueOnKey key replacement xs = map (\(k, v) => if k == key then (k, replacement) else (k, v)) xs

mutual
  storeChildDef : (key : String) 
                -> (NamespacedName, FC, NamedDef) 
                -> List (String, NestedDefs) 
                -> List (String, NestedDefs)
  storeChildDef key def children = case (lookup key children) of
                                        Nothing => (key, storeDef def initNestedDefs) :: children
                                        (Just nd) => replaceValueOnKey key (storeDef def nd) children

  storeDef : (NamespacedName, FC, NamedDef) -> NestedDefs -> NestedDefs
  storeDef (nsn, fc, nd) acc = case (consumeNameComponent nsn) of
                                    (Left name) => record { defs $= ((MkLeafDef name fc nd) ::) } acc
                                    (Right (path, rest)) => record { children $= (storeChildDef path (rest, fc, nd)) } acc

||| Group all function definitions by namespace
||| in a nested fashion so that we can export the
||| swift definitions in nested enums.
namespacedDefs : List (Name, FC, NamedDef) -> NestedDefs
namespacedDefs = (foldr storeDef initNestedDefs) . (map namespacedDef)

||| Compile a TT expression to Swift
compileToSwift : Ref Ctxt Defs -> Term [] -> Core String
compileToSwift c tm = do cdata <- getCompileData Cases tm
                         let ndefs = namespacedDefs $ namedDefs cdata
                         getScopeImps ndefs
                         -- defNames <- traverse id $ ?getImpH <$> ndefs
                         -- pure $ foldr (\s => (s ++ ", " ++)) "" defNames
                         -- ?hol

data SwiftExec = Interp | Compiler

findSwift : SwiftExec -> IO String
findSwift Interp = pure "swift"
findSwift Compiler = pure "swiftc"

||| Swift implementation of the `compileExpr` interface.
compileExpr : Ref Ctxt Defs 
            -> (tmpDir : String) 
            -> (outputDir : String) 
            -> ClosedTerm 
            -> (outfile : String) 
            -> Core (Maybe String)
compileExpr c tmpDir outputDir tm outfile
    = do swift <- compileToSwift c tm
         let out = outputDir </> outfile
         Right () <- coreLift (writeFile out swift)
            | Left err => throw (FileErr out err)
         pure (Just out)

||| Swift implementation of the `executeExpr` interface.
executeExpr : Ref Ctxt Defs -> (tmpDir : String) -> ClosedTerm -> Core ()
executeExpr c tmpDir tm
    = do let outn = tmpDir </> "_tmp_swift" ++ ".swift"
         swift <- compileToSwift c tm
         Right () <- coreLift $ writeFile outn swift
            | Left err => throw (FileErr outn err)
         swiftexec <- coreLift $ findSwift Interp
         coreLift $ system (swiftexec ++ " " ++ outn)
         pure ()

export
codegenSwift : Codegen
codegenSwift = MkCG compileExpr executeExpr
