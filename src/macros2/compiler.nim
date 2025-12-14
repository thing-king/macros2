
import compiler/[ast, lineinfos, idents]
import compiler/[options, modulegraphs, msgs]
import compiler/[modules, parser, renderer]
var conf = newConfigRef()
var cache = newIdentCache()

import strutils

import ./core/core

proc toNodeLineInfo(info: TLineInfo): NodeLineInfo =
  ## Convert compiler's TLineInfo to our NodeLineInfo
  # Use toFullPath or toFilename to get the actual filename string
  result.filename = conf.toFullPath(info.fileIndex)
  result.line = info.line.int
  result.column = info.col.int

proc convertToNode(n: PNode): Node =
  ## Convert a compiler NimNode (PNode) to our Node structure
  ## Internal function - NOT exported
  
  if n.isNil:
    return core.newNode(nkEmpty)
  
  result = core.newNode(parseEnum[NodeKind]($n.kind))
  result.info = toNodeLineInfo(n.info)
  
  # Convert based on node kind
  case n.kind
  of TNodeKind.nkStrLit..TNodeKind.nkTripleStrLit:
    result.strVal = n.strVal
  of TNodeKind.nkIdent:
    result.strVal = n.ident.s
  of TNodeKind.nkSym:
    result.strVal = n.sym.name.s
  of TNodeKind.nkCharLit..TNodeKind.nkUInt64Lit:
    result.intVal = n.intVal
  of TNodeKind.nkFloatLit..TNodeKind.nkFloat128Lit:
    result.floatVal = n.floatVal
  of TNodeKind.nkEmpty, TNodeKind.nkNilLit:
    discard
  else:
    # if Node has children
    result.children = @[]
    for child in n.sons:
      result.children.add(convertToNode(child))


proc parseStmt*(s: string): Node =
  ## Compiles the passed string to its AST representation.
  ## Expects one or more statements. Raises `ValueError` for parsing errors.
  ## Returns a Node (non-ref structure).
  
  # parseString comes from the included core_converter
  # It returns a NimNode (which is PNode internally)
  let nimNode = parseString(s, cache, conf)
  # discard
  # # Convert to our Node structure
  result = convertToNode(nimNode)
  
  # # Store the repr using the compiler's renderer
  # result.repr = repr(nimNode)