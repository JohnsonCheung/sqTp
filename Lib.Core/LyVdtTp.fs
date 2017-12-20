[<AutoOpen>]
module Lib.LyVdt
open Lib.Core
open Lib.Core.Types
type msgs = msg list
type linMsgs = lin*msgs
type endMsgs = msgs
type isChkFstTermDup = bool
type tp = lines
type tpOpt = tp option
type msgLy = ly
type linWdt = wdt
type msgTp = tp
type vdtTp = isEr * msgTp
type lyMsgs = msgs[]
type vdtMsgs = lyMsgs*endMsgs 
type chkr = ly -> vdtMsgs
let internal fmtLinMsgs(w:linWdt)(linMsgs:linMsgs):lines = 
    let lin,msgs = linMsgs
    if lisIsEmpty msgs then lin else
        let lin0 = 
            let msg0 = List.head msgs
            ( alignL w lin ) + msg0
        let linRst = 
            let linesRst = List.tail msgs |> jnCrLf
            linesTab "" w linesRst
        let o = lin0 + linRst
        o
let empVdtMsgs:vdtMsgs = [||],[]
let empChkr:chkr = fun(ly:ly)->empVdtMsgs
let dupFstTermChkr(ly:ly):vdtMsgs=(ly|>lyDupFstTermLyMsgs),[]
let isEmpLyMsgs(a:lyMsgs) = sz a = 0 || (a |> ayAny lisIsEmpty)
let lyMsgsAdd(a:lyMsgs)(b:lyMsgs) =
    let ca = sz a 
    let cb = sz b 
    if ca<>cb then er "{sz1} <> {sz2}, cannot add" [ca;cb]
    let o = a |> ayZip b |> ayMap (fun(a:msgs,b:msgs)->a@b)
    o
let vdtMsgsAdd(a:vdtMsgs)(b:vdtMsgs) =
    let lm1,em1 = a
    let lm2,em2 = b
    let lm,em = 
        match isEmpLyMsgs lm1, isEmpLyMsgs lm2 with
        | true,_ -> lm2,em2
        | _,true -> lm1,em1
        | _,_ ->
            let lm = lyMsgsAdd lm1 lm2
            let em = em1 @ em2
            lm,em
    lm,em
let isEmpVdtMsgs(a:vdtMsgs) = isEmpLyMsgs(fst a) || lisIsEmpty(snd a)
let isErVdtMsgs  = isEmpVdtMsgs >> not
let isErVdtMsgsLis = List.exists isErVdtMsgs
let fmtVdtMsgs(ly:ly)(a:vdtMsgs):lines =
    if isEmpVdtMsgs a then ly |> jnCrLf else
        let lm,em = a
        let linMsgsAy:linMsgs[] = ayZip ly lm
        let w = ssWdt ly + 1
        let lines = linMsgsAy|>ayMap(fmtLinMsgs w) |>jnCrLf
        let endLines = em |> lisToAy |> syAddPfx "--- " |> jnCrLf
        let pfx = if endLines = "" then "\r\n" else ""
        lines + pfx + endLines
let toVdtTp fstLinOpt (ly:ly)(a:vdtMsgs):vdtTp =
    let vdtMsgsTp(ly:ly)(a:vdtMsgs):vdtTp =
        let w = ssWdt ly
        let toLines(msgs:msgs,lin) = 
            if lisIsEmpty msgs then lin else
                let lin0 = 
                    let msg0 = List.head msgs
                    ( alignL w lin ) + msg0
                let linRst = 
                    let linesRst = List.tail msgs |> jnCrLf
                    linesTab "" w linesRst
                let o = lin0 + linRst
                o
        let lm,em = a
        let msgTp = (ly|>ayZip lm|> ayMap toLines|>ayToLis)@em|>jnCrLf
        //msgTp
        true,""
    let fstLin = if isSome fstLinOpt then fstLinOpt.Value + "\r\n" else ""
    let msgTp = fstLin + (fmtVdtMsgs ly a) 
    let isEr = isErVdtMsgs a
    let vdtTp = isEr,msgTp
    if true then failwith ""
    vdtTp
    true,msgTp
let lyVdt(chkrLis:chkr list)(isChkFstTerm:isChkFstTermDup)(ly:ly):vdtMsgs =
    let clnLy = ly|>lyRmv3DashRmk|>syRTrim 
    let apply chk = chk clnLy
    let mutable dupChkr = List.empty<chkr>
    if isChkFstTerm then dupChkr <- [fun(ly:ly)->(ly|>lyDupFstTermLyMsgs),[]]
    let vmLis = dupChkr@chkrLis |> lisMap apply
    let vm = vmLis |> lisFold vdtMsgsAdd empVdtMsgs 
    vm