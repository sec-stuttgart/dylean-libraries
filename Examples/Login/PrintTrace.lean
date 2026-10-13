module

import Examples.Login.Printing
import all Examples.Login.SanityChecks

/-- Emit only DY* JSON lines on stdout; report an unexpected failed run on stderr. -/
public def main : IO UInt32 := do
  let (result, tr) := DY.Example.Login.successfulLogin.run DY.Trace.nil
  let stdout ← IO.getStdout
  stdout.putStr (DY.Example.Login.loginTraceToString tr.val)
  if result == some true then
    return 0
  else
    let stderr ← IO.getStderr
    stderr.putStrLn "successfulLogin failed; stdout contains the trace up to failure."
    return 1
