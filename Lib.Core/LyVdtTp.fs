namespace Lib.LyVdt
open Lib.Core
type msgs = msg list
type linMsgs = lin*msgs
type endMsgs = msgs
type chkFstTermDup = bool
type tp = lines
type msgLy = ly
type linWdt = wdt
type msgTp = tp
type vdtTp = isEr * msgTp
type lyMsgs = msgs[]
type vdtMsgs = lyMsgs*endMsgs
type chkr = ly -> vdtMsgs
module LyMsgs =
    let linCnt(lyMsgs:lyMsgs) = sz lyMsgs
    let isEmpty lyMsgs = linCnt lyMsgs = 0 || (lyMsgs |> ayAny lisIsEmpty)
    let empty:lyMsgs = [||]
    let add a b:lyMsgs =
        if linCnt a <> linCnt b then er "{sz1} <> {sz2}, cannot add" [linCnt a;linCnt b]
        let lyMsgs = a |> ayZip b |> ayMap (fun(a:msgs,b:msgs)->a@b)
        lyMsgs
module LinMsgs =
    let lines(w:linWdt)(linMsgs:linMsgs):lines = 
        let lin,msgs = linMsgs
        match List.isEmpty msgs with
        | true -> lin
        | _ -> 
            let lin0 = 
                let msg0 = List.head msgs
                ( alignL w lin ) + msg0
            let linRst = 
                let linesRst = List.tail msgs |> jnCrLf
                linesTab "" w linesRst
            let o = lin0 + linRst
            o
module VdtMsgs =
    let isEmpty(vm:vdtMsgs) = 
        let lyMsgs,endMsgs = vm
        LyMsgs.isEmpty lyMsgs && lisIsEmpty endMsgs
    let lines(ly:ly)(vm:vdtMsgs):lines =
        if isEmpty vm then ly |> jnCrLf else
            let lyMsgs,endMsgs = vm
            let linMsgsAy:linMsgs[] = ayZip ly lyMsgs
            let w = ssWdt ly + 1
            let lines = linMsgsAy|>ayMap (LinMsgs.lines w) |>jnCrLf
            let endLines = endMsgs |> lisToAy |> syAddPfx "--- " |> jnCrLf
            let lines = if endLines="" then lines else lines+"\r\n"+endLines
            lines
    let isEr(a:vdtMsgs) = 
        let lm,em = a
        LyMsgs.isEmpty lm || (lisIsEmpty em)
    let msgsTp(ly)(a:vdtMsgs):msgTp =
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
        msgTp
    let add(a:vdtMsgs)(b:vdtMsgs):vdtMsgs =
        let lm1,em1 = a
        let lm2,em2 = b
        let lm,em = 
            match LyMsgs.isEmpty lm1 ,LyMsgs.isEmpty lm2 with
            | true,_ -> lm2,em2
            | _,true -> lm1,em1
            | _,_ ->
                let lm = LyMsgs.add lm1 lm2
                let em = em1 @ em2
                lm,em
        (lm,em)
    let empty = LyMsgs.empty,[]
    let vdtTp fstLinOpt (ly:ly)(vm:vdtMsgs): vdtTp = 
        let isEr = isEr vm
        let fstLin = if isSome fstLinOpt then fstLinOpt.Value + "\r\n" else ""
        let msgTp = fstLin + lines ly vm
        let vdtTp = isEr,msgTp
        vdtTp
module Chkr =
    let empty:chkr = fun(ly:ly)->VdtMsgs.empty
    let dupFstTermChkr:ly->vdtMsgs=fun(ly:ly)->(ly|>ly_dupFstTermLyMsgs),[]
module Ly =
    let vdtMsgs(chkrLis:chkr list)(chkFstTerm:chkFstTermDup)(ly:ly):vdtMsgs =
        let clnLy = ly|>ly_rmv3DashRmk|>syRTrim 
        let apply(chkr:chkr):vdtMsgs=chkr clnLy
        let l =
            if chkFstTerm then 
                let mkChkr:chkr=fun(ly:ly)->(ly|>ly_dupFstTermLyMsgs),[]
                mkChkr::chkrLis
            else
                chkrLis
        let vm = l |> lisMap apply |> lisFold VdtMsgs.add VdtMsgs.empty
        vm
