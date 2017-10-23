namespace Lib.Core
[<AutoOpen>]
module Alias = 
    let ayAll = Array.forall
    let ayAny = Array.exists
    let ayWh = Array.filter
    let ayMax = Array.max
    let ayMap = Array.map
    let lisAny = List.exists
    let lisAll = List.forall
    let lisWh = List.filter
    let lisPick = List.pick
    let lisTryPick = List.tryPick
[<AutoOpen>]
module Fail = 
    let fail s = failwith s |> ignore
module Str =
    open Microsoft.VisualBasic
    let left n s = Strings.Left(s,n)
    let right n s = Strings.Left(s,n)
    let len (s:string) = s.Length
    let mid p len (s:string) = s.Substring(p,len)
    let midFm p (s:string) = s.Substring(p)
    let trim s = Strings.Trim(s)
    let ltrim s = Strings.Trim(s)
    let rtrim s = Strings.RTrim(s)
    let spc n = Strings.Space(n)
    let split sep s = Strings.Split(s,sep)
    let rpl ss by s = Strings.Replace(s,ss,by)
    let rplOnce ss by s = Strings.Replace(s,ss,by,Count=1)
    let pos(ss:string)(s:string) = s.IndexOf(ss)
    let posRev(ss:string)(s:string) = s.LastIndexOf(ss)
    let brkAt p sep s =
        let s1 = left p s |> trim
        let s2 = midFm (p+(len sep)) s |> trim
        s1,s2
    
    let private b posF sep s = 
        let p = posF sep s 
        if p = -1 then fail("sep{" + sep + "} not s{" + s + "}")
        brkAt p sep s
    let brk    = b pos
    let brkRev = b posRev
    let brkSpc = brk " "
    let brkSpcRev = brkRev " "

    let private m1 s = s,""
    let private m2 s = "",s
    let private bb posF mkF sep s =
        let p = posF sep s
        if p = -1 then mkF s else
            brkAt p sep s
    let brk1 = bb pos m1
    let brk2 = bb pos m2
    let brk1Rev = bb posRev m1
    let brk2Rev = bb posRev m2
    let brk1Spc = brk1 " "
    let brk2Spc = brk2 " "
module Tak =
    open Str
    let takAftOrAll sep s = 
        let p = pos sep s
        if p = -1 then s else left p s
    let takAft sep s = midFm ((pos sep s)+(len sep)) s
    let takBef sep s = left (pos sep s) s
module Rmk = 
    open Tak
    open Str
    let rmv2DashRmk s = takAftOrAll "--" s |> rtrim
    let syRmv2DashRmk sy = sy |> ayMap rmv2DashRmk
module Predict =
    let pNot p a = p a |> not
    let pOr p1 p2 a = p1 a || p2 a
    let pAnd p1 p2 a = p1 a && p2 a
    let pAll pLis a = pLis |> lisAll (fun pd -> pd a)
    let pAny pLis a = pLis |> lisAny (fun pd -> pd a)
module Convert =
    let toStr a = sprintf "%A" a
    let olis(olis:obj list) = olis
    let ayToSy ay = [| for i in ay -> toStr i |]
    let oyToSy(oy:obj[]) = [| for i in oy -> toStr i |]
    let olisToSlis(olis:obj list) = [for i in olis -> toStr i]
module Ay =
    let x = 1
module MacroStr =
    let macroStrToSy macroStr : string[] = [||]
module Er =
    open MacroStr
    let er macroStr (olis:obj list) =1

module FtRead =
    open System.IO
    let ftStr ft = File.ReadAllText(ft) 
    let ftLy ft = File.ReadAllLines(ft)
module Jn =
    open Microsoft.VisualBasic
    open Convert
    let jnAy sep (ay:'a[]) = let sy = ayToSy ay in Strings.Join(sy,sep)
    let jnAyCrLf = jnAy "\r\n"
module Wrt =
    open System.IO
    open Convert
    open Jn
    let wrtStr ft s = File.WriteAllText(ft,s)
    let wrtAy ft ay = ayToSy ay |> jnAyCrLf |> wrtStr ft
module Shell =
    open Microsoft.VisualBasic
    type Sty = AppWinStyle
    let shell cmd = Interaction.Shell(cmd,Sty.MaximizedFocus) |> ignore
module Pth =
    let pthIsExists = System.IO.Directory.Exists
    let pthCrt pth = System.IO.Directory.CreateDirectory pth |> ignore
    let pthEns pth = if pthIsExists pth |> not then pthCrt pth
module Tmp =
    open Pth
    let mutable i = 0
    let timStmp() = i<-i+1; System.DateTime.Now.ToString("yyyymmdd_hhmmss_") + (string i)
    let tmpNm() = "T_" + timStmp()
    let tmpFn ext = tmpNm() + ext
    let tmpPth = (System.IO.Directory.s .SpecialFolder.ApplicationData()) + "FSharp\""
    pthEns tmpPth
    let tmpFt() = tmpPth + (tmpFn ".txt")
module Brw =
    open Shell
    let brwFt ft = shell("note.exe \"" + ft + "\"")
    let brwStr s = 
        let ft = tmpFt() 
        wrtStr ft s
        brwFt ft
namespace Lib.Dta
open Lib.Core
module Dr =
    fail "sdf"

namespace SqTp
open Lib.Core
module SqTp =
    open FtRead
    type Rslt = {sq': string option; edt':string option}
    let processRslt tpFt r =
        let {sq'=sq';tp'=tp'}
        let sqFt tpFt = ""
        wrtStrOpt tpFt tp'
        wrtStrOpt sqFt sq'
        ()
    let tpFtEvl ft =
        let sqTp = ftStr ft
        let r = SqTpEvl(sqTp)
        rsltProcess r
        r
    let main = tpFtEvl