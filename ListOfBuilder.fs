type LisOfBuilder() =
    member x.Yield m = [m]
    member x.YieldFrom m = m
    member x.Combine(a,f) = a@(f())
    member x.Delay f = fun()->f()
    member x.Return m = [m]
    member x.Zero() = 0
    member x.Run(f) = f()
let lisOf = new LisOfBuilder()
let a = lisOf {
        yield 1
        yield 2
        return 4
        return 5
    }
printfn "%A" a
