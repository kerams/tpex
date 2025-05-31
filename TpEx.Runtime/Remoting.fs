[<System.Runtime.CompilerServices.SkipLocalsInit>]
module FSharp.TpEx.Remoting

#if !FABLE_COMPILER

open System
open System.Buffers.Binary
open System.Text
open System.Net.Http
open System.Threading.Tasks
open Fable.Remoting.Json
open Newtonsoft.Json

let private converter = FableJsonConverter ()

type ProxyRequestException (response: HttpResponseMessage, errorMsg) = 
    inherit System.Exception (errorMsg)
    member _.StatusCode = response.StatusCode

let createBody arg =
    let s = JsonConvert.SerializeObject (arg, converter)
    new StringContent (s, Encoding.UTF8, "application/json")

let post (client: HttpClient) (url: string) arg = backgroundTask {
    use content = createBody [ arg ]
    use! response = client.PostAsync (url, content)
    let! responseData = response.Content.ReadAsByteArrayAsync()

    if response.IsSuccessStatusCode then
        return responseData
    elif response.StatusCode = System.Net.HttpStatusCode.InternalServerError then
        return raise (ProxyRequestException(response, sprintf "Internal server error (500) while making request to %s" url))
    elif response.StatusCode = System.Net.HttpStatusCode.Unauthorized then
        return raise (ProxyRequestException(response, sprintf "Unauthorized error from the server (401) while making request to %s" url))          
    elif response.StatusCode = System.Net.HttpStatusCode.Forbidden then
        return raise (ProxyRequestException(response, sprintf "Forbidden error from the server (403) while making request to %s" url))
    else
        return raise (ProxyRequestException(response, sprintf "Http error from server occured while making request to %s" url))
}

let inline fixstr len = 160uy + byte len
[<Literal>]
let Str8 = 0xd9uy
[<Literal>]
let Str16 = 0xdauy
[<Literal>]
let Str32 = 0xdbuy

let inline fixarr len = 144uy + byte len
[<Literal>]
let Array16 = 0xdcuy
[<Literal>]
let Array32 = 0xdduy

[<Literal>]
let Nil = 0xc0uy
[<Literal>]
let False = 0xc2uy
[<Literal>]
let True = 0xc3uy

let inline fixposnum value = byte value
let inline fixnegnum value = byte value ||| 0b11100000uy
[<Literal>]
let Uint8 = 0xccuy
[<Literal>]
let Uint16 = 0xcduy
[<Literal>]
let Uint32 = 0xceuy
[<Literal>]
let Uint64 = 0xcfuy

[<Literal>]
let Int8 = 0xd0uy
[<Literal>]
let Int16 = 0xd1uy
[<Literal>]
let Int32 = 0xd2uy
[<Literal>]
let Int64 = 0xd3uy

[<Literal>]
let Bin8 = 0xc4uy

let inline readInt16 (data, pos: int ref) =
    pos.Value <- pos.Value + 3
    BinaryPrimitives.ReadInt16BigEndian (Span.op_Implicit (data.AsSpan (pos.Value - 2, 2)))

let inline readInt32 (data, pos: int ref) =
    pos.Value <- pos.Value + 5
    BinaryPrimitives.ReadInt32BigEndian (Span.op_Implicit (data.AsSpan (pos.Value - 4, 4)))

let inline readInt64 (data, pos: int ref) =
    pos.Value <- pos.Value + 9
    BinaryPrimitives.ReadInt64BigEndian (Span.op_Implicit (data.AsSpan (pos.Value - 8, 8)))

let deserInt64 (data: byte[], pos: int ref) =
    match data.[pos.Value] with
    // fixposnum
    | b when b ||| 0b01111111uy = 0b01111111uy ->
        pos.Value <- pos.Value + 1
        int64 b
    // fixnegnum
    | b when b ||| 0b00011111uy = 0b11111111uy ->
        pos.Value <- pos.Value + 1
        sbyte b |> int64
    | Uint8 ->
        pos.Value <- pos.Value + 2
        int64 data.[pos.Value - 1]
    | Uint16 ->
        readInt16 (data, pos) |> int64
    | Uint32 ->
        readInt32 (data, pos) |> int64
    | Uint64 ->
        readInt64 (data, pos)
    | b ->
        failwithf "Expected int64, got format %d" b

let deserInt32 (data: byte[], pos: int ref) =
    match data.[pos.Value] with
    // fixposnum
    | b when b ||| 0b01111111uy = 0b01111111uy ->
        pos.Value <- pos.Value + 1
        int b
    // fixnegnum
    | b when b ||| 0b00011111uy = 0b11111111uy ->
        pos.Value <- pos.Value + 1
        sbyte b |> int
    | Uint8 ->
        pos.Value <- pos.Value + 2
        int data.[pos.Value - 1]
    | Uint16 ->
        readInt16 (data, pos) |> int
    | Uint32 ->
        readInt32 (data, pos)
    | b ->
        failwithf "Expected int32, got format %d" b

let deserInt16 (data: byte[], pos: int ref) =
    match data.[pos.Value] with
    // fixposnum
    | b when b ||| 0b01111111uy = 0b01111111uy ->
        pos.Value <- pos.Value + 1
        int16 b
    // fixnegnum
    | b when b ||| 0b00011111uy = 0b11111111uy ->
        pos.Value <- pos.Value + 1
        sbyte b |> int16
    | Uint8 ->
        pos.Value <- pos.Value + 2
        int16 data.[pos.Value - 1]
    | Uint16 ->
        readInt16 (data, pos)
    | b ->
        failwithf "Expected int16, got format %d" b

let inline deserDateTimeOffset (data, pos: int ref) =
    DateTimeOffset (deserInt64 (data, pos), TimeSpan.FromMinutes (deserInt64 (data, pos) |> float))

let inline deserUnit (_data: byte[], pos: int ref) =
    pos.Value <- pos.Value + 1

let inline deserGuid (data: byte[], pos: int ref) =
    match data.[pos.Value] with
    | Bin8 ->
        // also skipping length
        pos.Value <- pos.Value + 18
        Guid (data.AsSpan (pos.Value - 16, 16))
    | b ->
        failwithf "Expected bin8 for guid, got format %d" b

let inline deserBoolean (data: byte[], pos: int ref) =
    pos.Value <- pos.Value + 1
    match data.[pos.Value - 1] with
    | True -> true
    | False -> false
    | b ->
        failwithf "Expected bool, got format %d" b

let deserString (data: byte[], pos: int ref) =
    let len =
        match data.[pos.Value] with
        // fixstr
        | b when b ||| 0b00011111uy = 0b10111111uy ->
            let len = b &&& 0b00011111uy |> int
            pos.Value <- pos.Value + len
            len
        | Str8 ->
            let len = data.[pos.Value + 1] |> int
            pos.Value <- pos.Value + len + 1
            len
        | Str16 ->
            let len = BinaryPrimitives.ReadUInt16BigEndian (Span.op_Implicit (data.AsSpan (pos.Value + 1, 2))) |> int
            pos.Value <- pos.Value + len + 3
            len
        | Str32 ->
            let len = BinaryPrimitives.ReadUInt32BigEndian (Span.op_Implicit (data.AsSpan (pos.Value + 1, 4))) |> int
            pos.Value <- pos.Value + len + 5
            len
        | b ->
            failwithf "Expected string, got format %d" b

    Encoding.UTF8.GetString (data, pos.Value - len, len)

let inline deserTimeOnly (data: byte[], pos: int ref) =
    deserInt64 (data, pos) |> TimeOnly

let inline deserDateOnly (data: byte[], pos: int ref) =
    DateOnly.FromDayNumber (deserInt32 (data, pos))

let readArrayLength (data: byte[], pos: int ref) =
    match data.[pos.Value] with
    | b when b ||| 0b00001111uy = 0b10011111uy ->
        let len = b &&& 0b00001111uy |> int
        pos.Value <- pos.Value + 1
        len
    | Array16 ->
        let len = BinaryPrimitives.ReadUInt16BigEndian (Span.op_Implicit (data.AsSpan (pos.Value + 1, 2))) |> int
        pos.Value <- pos.Value + len + 3
        len
    | Array32 ->
        let len = BinaryPrimitives.ReadUInt32BigEndian (Span.op_Implicit (data.AsSpan (pos.Value + 1, 4))) |> int
        pos.Value <- pos.Value + len + 5
        len
    | b ->
        failwithf "Expected array-encoded type, got format %d" b

#endif
