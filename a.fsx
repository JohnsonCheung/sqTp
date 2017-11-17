#r @"C:\Users\user\Source\Repos\Sql3\Lib.Core\bin\Debug\Lib.Core.exe"
open Lib.Core
open Lib.SqTp1.H
//let swLin_msgs(prm:prmSdic)(sw:swSdic)(swLin:swLin):msgs=
let prm,sw,swLin = empSdic,empSdic,"?lskdfjdsf AND "
let k,opStr,termLvs = brk3Term swLin
let termAy = splitLvs termLvs
let opSSS = toUpper opStr
let cPfxQ()=fstChr k <> "?"
let cOp()=opSSS |> isInLisI ["EQ";"NE";"AND";"OR"] |> not
let cAndOr() = opSSS |> isInLisI ["EQ";"NE"]
let cMin3T()=opSSS |> isInLisI ["AND";"OR"] && sz termAy < 1
let cEq4T()=sz termAy <> 2
let pP = hasPfx "%"
let pS = hasPfx "?"
let notInSw = notInDic sw
let notInPrm = notInDic prm
let cPS()=isAll(pS .| pP)(termAy)
let cOutSw() =termAy|>ayWh pS|>isAny notInSw
let cOutPrm()=termAy|>ayWh pP|>isAny notInPrm
let mPfxQ()=["must begin with ?"]
let mOp()=["2nd term is operator, it must be [NE EQ OR AND]"]
let mAndOr()=[]
let mMin3T()=["when 2nd term is [AND|OR], it must have at least 3 terms"]
let mEq4T()=["when 2nd term is [EQ|NE], it must have 4 terms"]
let mPS()=
    let er = (pS .&  notInDic sw) .| (pP .& notInDic prm)       
    let erTermLis = termAy |> ayWh er |> ayToLis
    if lisIsEmpty erTermLis then [] else 
        let s = jnSpc erTermLis
        let msg = fmtQQ "Following terms must has pfx [%] [?]: [?]" ["?";s]
        [msg]
let mOutSw() = ["some term is not in Sw"]
let mOutPrm() = ["some term is not in Prm"]
let f c m:msgs->msgs = fun(msgs:msgs)->if lisIsEmpty msgs then (if c() then m() else []) else msgs 
let pfxQ  = f cPfxQ  mPfxQ  
let op    = f cOp    mOp 
let andOr = f cAndOr mAndOr
let min3T = f cMin3T mMin3T
let eq4T  = f cEq4T  mEq4T
let pq    = f cPS    mPS
let outSw = f cOutSw  mOutSw
let outPrm= f cOutPrm mOutPrm
let and2(f1:msgs->msgs)(f2:msgs->msgs)(msgs:msgs):msgs=f1 msgs @ f2 msgs 
let or2(f1:msgs->msgs)(f2:msgs->msgs)(msgs:msgs):msgs=f1 msgs @ f2 msgs 
let (.&) = and2
let (.|) = or2
let er1 = pfxQ .| op .| (andOr .& min3T )
let er = pfxQ .| op .| ( andOr .& min3T ) .| eq4T .| pq .| outSw .| outPrm
let msgs = er1 []
msgs

(*
//Aim: Try to find BkAyToLyOpt
type BkTy = PrmBk | SwBk | SqBk | RmkBk | ErBk
type Bk = {ty:BkTy;ly:string[]}
let BkTy(b:Bk)=b.ty
let BkLy(b:Bk)=b.ly
let optVal(a:'a option) = a.Value
let optMap f (a:'a option) = if(a.IsSome) then Some(f a.Value) else None
let ayFindOpt = Array.tryFind
let eq a b = a = b
//let BkAyToLyOpt ty = BkTy >> eq ty |> ayFindOpt >> optMap BkLy
let BkAyToLyOpt ty b =
    let b' = b |> ayFindOpt (BkTy >> eq ty)
    if b'.IsSome then Some(b'.Value.ly) else None
let BkAy = 
    [|
        {ty=PrmBk;ly=[|"a";"b"|]}
        {ty=SwBk;ly=[|"a";"b"|]}
        {ty=PrmBk;ly=[|"a";"b"|]}
    |]
let lyOpt = BkAyToLyOpt PrmBk BkAy
lyOpt
*)