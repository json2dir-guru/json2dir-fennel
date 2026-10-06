# json2dir-fennel

json2dir in Fennel: builds the directory tree a JSON document describes, using LuaJIT's FFI for libc calls.

    fennel --compile json2dir.fnl > out/json2dir.lua && luajit out/json2dir.lua < tree.json
