# Protocol JSON format

The `swarmgate` binary and the Python front-end exchange protocols and events as JSON. The DSL compiler
(`swarmgate-py compile`) emits this; you can also write it by hand.

## Protocol

```json
{
  "name": "ApprovalGate",
  "roles": ["User", "Agent", "Human", "Shell"],
  "start": 0,
  "final": [7],
  "budget": 1000,
  "maxStrikes": 3,
  "states": [
    [ {"src":0,"dst":1,"label":"Task","ty":"str","pred":{"lenLe":[[],2000]},"next":1} ],
    ...
  ],
  "properties": [ {"name":"NoUnapprovedExec", "formula": {...}} ],
  "ifc": {"untrusted":[2], "endorsers":[2], "maxBits":8, "sensitive":[{"src":null,"dst":3,"label":null}]},
  "locals": [ {"start":0,"states":[ [ {"dir":"send","peer":1,"label":"Task","ty":"str","pred":true,"next":1} ] ]}, ... ]
}
```

* `states[i]` is the list of outgoing transitions of state `i`.
* A transition is `{src, dst, label, ty, pred, next}` (role indices into `roles`).
* `final` lists accepting states; a session is complete in a final state with no outgoing transitions.
* `ifc`, `properties`, `locals` are optional; `locals` (projections) enables the decentralised check.

## Types (`ty`)

```
"unit" | "bool" | "int" | "str"
{"enum": ["ls","cat"]}
{"list": <ty>}
{"record": [["cmd", <ty>], ["arg", <ty>]]}     // closed: value must have exactly these fields
```

`int` is 64-bit bounded. Information capacity: `unit`=0, `bool`=1, `enum(k)`=⌈log₂k⌉, `int`=64, `str`/`list`=∞.

## Refinements (`pred`)

```
true | false
{"and":[p,q]} | {"or":[p,q]} | {"not":p}
{"intLe":[path,k]} | {"intGe":[path,k]}          // path is a list of field names; [] = whole value
{"lenLe":[path,k]}                                // string length or list length ≤ k
{"strIn":[path,["a","b"]]}                        // value ∈ set
{"strNotContains":[path,";"]}                     // substring absent
{"eqStr":[path,"x"]} | {"eqBool":[path,true]}
```

## Past-time LTL (`formula`)

```
true | false
{"atom": {"src":0|null, "dst":1|null, "label":"Exec"|null}}   // null = wildcard
{"not":f} | {"and":[f,g]} | {"or":[f,g]} | {"imp":[f,g]}
{"prev":f} | {"once":f} | {"hist":f} | {"since":[f,g]}
```

## Events (gate input)

```json
{"src": 1, "dst": 3, "label": "exec", "payload": {"cmd":"df","arg":"-h"}}
```

Payloads are plain JSON (null = unit).

## Monitor server (`swarmgate serve protocol.json`)

JSON-lines request/response over stdin/stdout. Requests:

```json
{"op":"send", "session":"s1", "sender":1, "event":{...}}   → {"verdict":"deliver"|"reject", "reason":..., "blamed":..., "state":..., "count":..., "taint":[...], ...}
{"op":"kill",  "session":"s1"}
{"op":"reset", "session":"s1"}
{"op":"state", "session":"s1"}
```

`sender` is the authenticated principal (role index); `event.src` is the claimed source. A mismatch is the
`spoof` rejection.
