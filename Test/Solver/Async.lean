import Smt

open Lean Elab Meta

namespace SmtTest.Async

inductive EventKind where
  | query
  | rawSat
  | rawUnsat
  | rawUnknown
  | rawError
  | resultSat
  | resultUnsat
  | resultUnknown
  | exception
deriving BEq, Repr

def EventKind.ofOutput : Smt.AsyncOutput → EventKind
  | .queryString _ => .query
  | .rawResult (.ok (.sat _)) => .rawSat
  | .rawResult (.ok (.unsat _ _)) => .rawUnsat
  | .rawResult (.ok (.unknown _)) => .rawUnknown
  | .rawResult (.error _) => .rawError
  | .result (.sat _) => .resultSat
  | .result (.unsat _ _) => .resultUnsat
  | .result (.unknown _) => .resultUnknown
  | .exception _ => .exception

def collectEvents (ch : Std.CloseableChannel ((Name × Nat) × Smt.AsyncOutput)) :
    BaseIO (Array ((Name × Nat) × EventKind)) := do
  let mut events := #[]
  while let some (id, output) ← Std.CloseableChannel.tryRecv ch do
    events := events.push (id, .ofOutput output)
  return events

def assertEvents (actual expected : Array ((Name × Nat) × EventKind)) : TermElabM Unit := do
  unless actual == expected do
    throwError "unexpected asynchronous SMT events\nactual:   {repr actual}\nexpected: {repr expected}"

def assertCallerOwns (ch : Std.CloseableChannel ((Name × Nat) × Smt.AsyncOutput)) :
    TermElabM Unit := do
  if ← Std.CloseableChannel.isClosed ch then
    throwError "the SMT call unexpectedly closed its caller-owned channel"
  Std.CloseableChannel.Sync.close ch

def runSmt (cfg : Smt.Config) (goalType : Expr) : TermElabM Smt.Result := do
  let goal ← mkFreshExprMVar goalType
  Smt.smt cfg goal.mvarId! #[]

elab "#test_smt_async_order" : command => Command.liftTermElabM do
  let name := `async.order
  let ch ← Smt.initAsyncState name none true true true
  let sat ← runSmt {} (mkConst ``False)
  unless sat matches .sat none do
    throwError "expected the first SMT call to return sat"
  let unsat ← runSmt { trust := true } (mkConst ``True)
  unless unsat matches .unsat _ _ do
    throwError "expected the second SMT call to return unsat"
  assertEvents (← collectEvents ch) #[
    ((name, 0), .query),
    ((name, 0), .rawSat),
    ((name, 0), .resultSat),
    ((name, 1), .query),
    ((name, 1), .rawUnsat),
    ((name, 1), .resultUnsat)
  ]
  assertCallerOwns ch

elab "#test_smt_async_unknown" : command => Command.liftTermElabM do
  let name := `async.unknown
  let ch ← Smt.initAsyncState name none true true true
  let result ← runSmt { extraSolverOptions := [("rlimit-per", "1")] } (mkConst ``False)
  unless result matches .unknown _ do
    throwError "expected the resource-limited SMT call to return unknown"
  assertEvents (← collectEvents ch) #[
    ((name, 0), .query),
    ((name, 0), .rawUnknown),
    ((name, 0), .resultUnknown)
  ]
  assertCallerOwns ch

elab "#test_smt_async_exception" : command => Command.liftTermElabM do
  let name := `async.exception
  let ch ← Smt.initAsyncState name none true true true
  let threw ← try
    let _ ← runSmt { extraSolverOptions := [("not-a-cvc5-option", "true")] }
      (mkConst ``False)
    pure false
  catch _ => pure true
  unless threw do
    throwError "expected the invalid cvc5 option to throw"
  -- A second call must still be able to use the same caller-owned channel.
  let result ← runSmt {} (mkConst ``False)
  unless result matches .sat none do
    throwError "expected the SMT call after an exception to return sat"
  assertEvents (← collectEvents ch) #[
    ((name, 0), .query),
    ((name, 0), .rawError),
    ((name, 0), .exception),
    ((name, 1), .query),
    ((name, 1), .rawSat),
    ((name, 1), .resultSat)
  ]
  assertCallerOwns ch

elab "#test_smt_async_flags" : command => Command.liftTermElabM do
  for sendQuery in [false, true] do
    for sendRawResult in [false, true] do
      for sendResult in [false, true] do
        let name := Name.mkSimple s!"async.flags.{sendQuery}.{sendRawResult}.{sendResult}"
        let ch ← Smt.initAsyncState name none sendQuery sendRawResult sendResult
        let result ← runSmt {} (mkConst ``False)
        unless result matches .sat none do
          throwError "expected flag-combination SMT call to return sat"
        let mut expected := #[]
        if sendQuery then expected := expected.push ((name, 0), .query)
        if sendRawResult then expected := expected.push ((name, 0), .rawSat)
        if sendResult then expected := expected.push ((name, 0), .resultSat)
        assertEvents (← collectEvents ch) expected
        assertCallerOwns ch
  -- In particular, `sendResult := false` also suppresses UNSAT results. The experimental
  -- implementation applied this flag inconsistently across result variants.
  let name := `async.flags.unsat
  let ch ← Smt.initAsyncState name none false false false
  let result ← runSmt { trust := true } (mkConst ``True)
  unless result matches .unsat _ _ do
    throwError "expected the flag-suppression SMT call to return unsat"
  assertEvents (← collectEvents ch) #[]
  assertCallerOwns ch
  -- Exceptions are terminal protocol events rather than an optional result category.
  let name := `async.flags.exception
  let ch ← Smt.initAsyncState name none false false false
  let threw ← try
    let _ ← runSmt { extraSolverOptions := [("not-a-cvc5-option", "true")] }
      (mkConst ``False)
    pure false
  catch _ => pure true
  unless threw do
    throwError "expected the all-flags-disabled SMT call to throw"
  assertEvents (← collectEvents ch) #[((name, 0), .exception)]
  assertCallerOwns ch

elab "#test_smt_async_veil_defaults" : command => Command.liftTermElabM do
  let name := `async.veilDefaults
  let suppliedChannel ← Std.CloseableChannel.new
  let _ ← Smt.initAsyncState name (some suppliedChannel)
  let result ← runSmt {} (mkConst ``False)
  unless result matches .sat none do
    throwError "expected the default-config SMT call to return sat"
  assertEvents (← collectEvents suppliedChannel) #[((name, 0), .resultSat)]
  assertCallerOwns suppliedChannel

end SmtTest.Async

#test_smt_async_order
#test_smt_async_unknown
#test_smt_async_exception
#test_smt_async_flags
#test_smt_async_veil_defaults
