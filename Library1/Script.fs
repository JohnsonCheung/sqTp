// Learn more about F# at http://fsharp.org. See the 'F# Tutorial' project
// for more guidance on F# programming.
// Define your library scripting code here
//#r @"C:\Users\user\Source\Repos\Sql3\Lib.Core\bin\Debug\Lib.Core.exe"
//#r @"C:\Users\user\Source\Repos\Sql3\SqTp\bin\Debug\SqTp.exe"
//#r @"C:\Program Files (x86)\Reference Assemblies\Microsoft\Framework\.NETFramework\v4.6.1\PresentationFramework.dll"
[<AutoOpen>]
module AA =
    let a = 1
[<AutoOpen>]
module BB =
    let a = 2
open System.Windows
System.Windows.MessageBox.Show(AA.a.ToString()) |> ignore
let x = 1
let y = System.Console.In.ReadLine()