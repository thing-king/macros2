import macros
import tables


macro CacheTable*(name: static[string]): untyped =
  result = quote do:
    block:
      if `name` notin runtimeTables:
        runtimeTables[`name`] = newTable[string, core.Node]()
      runtimeTables[`name`]

import ./core/core
var runtimeTables* {.global.}: Table[string, ref Table[string, core.Node]]