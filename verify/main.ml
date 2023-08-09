open Extraction

type command = ((sym * dir) * state) option
type tm = state * sym -> command

let verify_cycler tm n =
    let n = nat_of_int n in
    ECyclers.verify_cycler tm n n

let verify_tcycler tm dir n0 n1 k =
    let n0 = nat_of_int n0
    and n1 = nat_of_int n1
    and k = nat_of_int k in
    ETranslatedCyclers.verify_tcycler tm dir n0 n1 k

let verify_backwards tm n =
    let n = nat_of_int n in
    EBackwardsReasoning.verify_backwards tm n

let seed_file = open_in_bin "../seed.dat"
let cert_file = open_in_bin "../certs.dat"
let index_file = open_out_bin "../decided.dat"

let read_u8 (ch: in_channel): int =
    Char.code (input_char ch)

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
    | 0 -> S0
    | 1 -> S1
    | _ -> failwith "invalid byte for symbol"

let parse_dir (c: char): dir =
    match Char.code c with
    | 0 -> R
    | 1 -> L
    | _ -> failwith "invalid byte for direction"

let parse_state (c : char): state option =
    match Char.code c with
    | 0 -> None
    | 1 -> Some A
    | 2 -> Some B
    | 3 -> Some C
    | 4 -> Some D
    | 5 -> Some E
    | _ -> failwith "invalid byte for state"

let read_tm (index: int): tm =
    seek_in seed_file (30 + 30 * index);
    let buf = Bytes.create 30 in
    really_input seed_file buf 0 30;
    let parse_cmd (i: int): command =
        let offset = 3 * i in
        match parse_state (Bytes.get buf (offset + 2)) with
        | None -> None
        | Some next ->
            let symbol = parse_symbol (Bytes.get buf offset) in
            let dir = parse_dir (Bytes.get buf (offset + 1)) in
            Some ((symbol, dir), next)
        in
    let commands = Array.init 10 parse_cmd in
    fun (q, s) ->
        let q = match q with
                | A -> 0
                | B -> 1
                | C -> 2
                | D -> 3
                | E -> 4
                in
        let i = match s with
                | S0 -> 2 * q
                | S1 -> 2 * q + 1
                in
        Array.get commands i

type cert =
    | CertCyclers of int
    | CertTCyclers of dir * int * int * int
    | CertBackwards of int

exception BadCert of int * cert

let show_cert (cert: cert): string =
    match cert with
    | CertCyclers n ->
        Printf.sprintf "CertCyclers %d" n
    | CertTCyclers (L, n0, n1, k) ->
        Printf.sprintf "CertTCyclers (L, %d, %d, %d)" n0 n1 k
    | CertTCyclers (R, n0, n1, k) ->
        Printf.sprintf "CertTCyclers (R, %d, %d, %d)" n0 n1 k
    | CertBackwards n ->
        Printf.sprintf "CertBackwards %d" n

let show_exn (e: exn): string option =
    match e with
    | BadCert (index, cert) ->
        Some (Printf.sprintf "BadCert (%d, %s)" index (show_cert cert))
    | _ -> None

let _ = Printexc.register_printer show_exn

let read_cert (): int * cert =
    let index = read_u32 cert_file in
    let cert = match read_u8 cert_file with
    | 0 -> CertCyclers (read_u32 cert_file)
    | 1 ->
        let dir = parse_dir (input_char cert_file)
        and n0 = read_u32 cert_file
        and n1 = read_u32 cert_file
        and k = read_u32 cert_file in
        CertTCyclers (dir, n0, n1, k)
    | 2 -> CertBackwards (read_u32 cert_file)
    | _ -> failwith "unknown certificate type"
    in (index, cert)

let verify_cert (index: int) (cert: cert): unit =
    let tm = read_tm index in
    let ok = match cert with
    | CertCyclers n -> verify_cycler tm n
    | CertTCyclers (dir, n0, n1, k) -> verify_tcycler tm dir n0 n1 k
    | CertBackwards n -> verify_backwards tm n
    in
    if ok then
        write_u32 index_file index
    else
        raise (BadCert (index, cert))

let rec verify () =
    let (index, cert) = read_cert () in
    verify_cert index cert;
    verify ()

let _ = try verify () with End_of_file -> ()
