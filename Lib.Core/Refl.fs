#nowarn "40" 
#nowarn "64" 
namespace Lib.Refl
open Lib.Core
[<AutoOpen>]
module Asm =
    open System.Reflection
    let asmLis(asm:Assembly) = 
        (*
        let a:Assembly = null
        a.LoadModule ppDomain.CurrentDomain.ActivationContext.
        let x = System.Diagnostics.Process.GetCurrentProcess().Modules
        [ for i in x do yield i.FileName ]
        *)
        asm
        