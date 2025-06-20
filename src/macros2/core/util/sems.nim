import compiler/[
  options, modulegraphs, ic/ic, ast, semdata
]

import intsets

export PContext

proc newContext*(graph: var ModuleGraph; module: PSym): PContext =
  new(result)
  result.optionStack = @[newOptionEntry(graph.config)]
  result.libs = @[]
  result.module = module
  result.friendModules = @[module]
  result.converters = @[]
  result.patterns = @[]
  result.includedFiles = initIntSet()
  # initStrTable(result.pureEnumFields)
  result.pureEnumFields = initStrTable()
  # initStrTable(result.userPragmas)
  result.userPragmas = initStrTable()
  result.generics = @[]
  result.unknownIdents = initIntSet()
  result.cache = graph.cache
  result.graph = graph
  # initStrTable(result.signatures)
  result.signatures = initStrTable()
  result.features = graph.config.features
  if graph.config.symbolFiles != disabledSf:
    let id = module.position
    # assert graph.packed[id].status in {undefined, outdated}
    # graph.packed[id].status = storing
    graph.packed[id].module = module
    initEncoder graph, module

proc semBindSym*(c: PContext, n: PNode): PNode =
  result = copyNode(n)
  result.add(n[0])