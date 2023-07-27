open Cyclers

type sym = bool
type state = int
type command = ((sym * dir) * state) option

let verify_cycler tm n =
    let n = nat_of_int n in
    verify_cycler 0 false (=) (=) tm n n

let seed_file = open_in_bin "../seed.dat"
let cert_file = open_in_bin "../certs.dat"
let index_file = open_out_bin "../decided.dat"

let read_u32 (ch: in_channel): int =
    let buf = Bytes.create 4 in
    really_input ch buf 0 4;
    let b i = Char.code (Bytes.get buf i) in
    let x0 = Int.shift_left (b 0) 24
    and x1 = Int.shift_left (b 1) 16
    and x2 = Int.shift_left (b 2) 8
    and x3 = Int.shift_left (b 3) 0 in
    Int.logor (Int.logor x0 x1) (Int.logor x2 x3)

let write_u32 (ch: out_channel) (v: int) =
    let b i = Char.chr (Int.logand (Int.shift_right v i) 255) in
    output_char ch (b 24);
    output_char ch (b 16);
    output_char ch (b 8);
    output_char ch (b 0)

let parse_symbol (c: char): sym =
    match Char.code c with
    | 0 -> false
    | 1 -> true
    | _ -> failwith "invalid byte for symbol"

let parse_dir (c: char): dir =
    match Char.code c with
    | 0 -> R
    | 1 -> L
    | _ -> failwith "invalid byte for direction"

let read_tm (index: int): (state, sym) tM =
    seek_in seed_file (30 + 30 * index);
    let buf = Bytes.create 30 in
    really_input seed_file buf 0 30;
    let parse_cmd (i: int): command =
        let offset = 3 * i in
        let symbol = parse_symbol (Bytes.get buf offset) in
        let dir = parse_dir (Bytes.get buf (offset + 1)) in
        let next = Char.code (Bytes.get buf (offset + 2)) in
        if next = 0 then
            None
        else
            Some ((symbol, dir), next - 1)
        in
    let commands = Array.init 10 parse_cmd in
    fun (q, s) ->
        let i = match s with
                | false -> 2 * q
                | true -> 2 * q + 1
                in
        Array.get commands i

type cert =
    | CertCyclers of int

let read_cert (): int * cert =
    let index = read_u32 cert_file in
    let cert = match read_u32 cert_file with
    | 0 -> CertCyclers (read_u32 cert_file)
    | _ -> failwith "unknown certificate type"
    in (index, cert)

let verify_cert (index: int) (cert: cert): unit =
    let tm = read_tm index in
    let ok = match cert with
    | CertCyclers n -> verify_cycler tm n
    in
    if ok then
        write_u32 index_file index
    else
        failwith "verification failed"

let rec verify () =
    let (index, cert) = read_cert () in
    verify_cert index cert;
    verify ()

let _ = try verify () with End_of_file -> ()
