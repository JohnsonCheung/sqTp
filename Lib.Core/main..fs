module main
open Lib.LyVdt
open Lib.Core
open Lib.SqTp2

[<EntryPoint>]
let main args = 
    let a = SqTpNm("SqTp").sqTp
//    let b = a.evl
    Seq().dupFmTo()
//    let b = a.evl
    Ay().ayRplByFmTo()
    Term().combineSamFstTerm()
    if false then
        (*
        let ft = TstDta.sqTpFt
        let {sq'=sq';tp'=tp'} = sqTpFtEvl ft
        if isSome tp' then brwFt ft
        if isSome sq' then brwFt (toSqFt ft)
        *)
        ()
    0