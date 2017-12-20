[<AutoOpen>]
module Lib.Core.Builders
// Builder
type MsgsBuilder()=
    member x.Yield m=false,[m]
    member x.Return(_)=true,[]
    member x.Combine(m,f)=
        match m with
        | false,aMsgs->
            let bRet,bMsgs = f()
            bRet,aMsgs@bMsgs
        | true,_->m
    member x.Delay f=fun()->f()
    member x.Run(f):msgs = f() |> snd
    member x.Zero()= false,[]
let msgs = new MsgsBuilder()
type YieldRetBuilder() =
    member x.Yield m=false,[m]
    member x.Return(_)=true,[]
    member x.Combine(m,f)=
        match m with
        | false,aLis->
            let bRet,bLis = f()
            bRet,aLis@bLis
        | true,_->m
    member x.Delay(f)=fun()->f()
    member x.Run(f) = f()|>snd
    member x.Zero() = []
type MayBeBuilder() = 
    member x.Return m = Some m
    member x.Zero() = None 
    member x.Combine(a:'a option,b) = if a.IsNone then None else b
    member x.Delay f = f()
type RetBuilder() =
    member x.Zero() = None
    member x.Return m = Some(m)
    member x.Combine(m:'a option,f) = if m.IsSome then m else f()
    member x.Delay(f)=fun()->f()
    member x.Run(f)=f()|>fun(a:'a option)->a.Value
type AnyTrueBuilder() =
    member x.Return m = m
    member x.Zero() = false
    member x.Combine(a,b) = if(a)then true else b
    member x.Delay(f) = f()
type LisOfBuilder() =
    member x.Zero() = None
    member x.Return m = m
    member x.Combine(a,b) = match a with None -> b | Some a -> b@[a]
type OneOfBuilder() = 
    member x.Zero() = None
    member x.Return m = Some m
    member x.Combine(a,b) = match a with None -> b | _ -> a
    member x.Delay(f) = f()
type ShortCutBuilder() = 
    member x.Zero() = None
    member x.Return m = Some m
    member x.ReturnFrom _ = Some None
    member x.Combine(a,b) = match a with None -> b | _ -> a
    member x.Delay(f) = f()
let shortCut = ShortCutBuilder()
let oneOf = OneOfBuilder()
let ret = RetBuilder()
let lisOf = LisOfBuilder()
let mayBe = MayBeBuilder()
let anyTrue = AnyTrueBuilder()

