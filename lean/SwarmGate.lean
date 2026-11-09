/-
  SwarmGate: Lean-verified session protocols as a reference monitor for multi-agent communication.

  Module map (see docs/THEORY.md):
    Basic       payload values, types, refinements                      §2
    Protocol    guarded automata, executable semantics, adequacy        §3
    Monitor     the gate; T1 enforcement, T2 transparency, T3 blame     §4
    Cert        certificate checking (translation validation)          §5.1
    Observe     protocol × observer products
    PTLTL       past-time temporal properties; T4 property transfer     §5.2
    Taint       context taint / IFC; T5                                 §5.3
    Liveness    T7 no-stuck, completion, bounded length                 §7
    Projection  decentralised sidecars; T6                              §6
    Noninterference  arbitrary agents; T9 noninterference, T9b budget   §5.4
    Admission   untrusted protocol authors; T8 meta-policy admission     §5.5
    Json, Analyze   untrusted glue and certificate generation
-/
import SwarmGate.Basic
import SwarmGate.Protocol
import SwarmGate.Monitor
import SwarmGate.Cert
import SwarmGate.Observe
import SwarmGate.PTLTL
import SwarmGate.Taint
import SwarmGate.Liveness
import SwarmGate.Projection
import SwarmGate.Admission
import SwarmGate.Noninterference
import SwarmGate.Bridge
import SwarmGate.Json
import SwarmGate.Analyze
