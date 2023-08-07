open Skelet1

(*
type conf = (direction * lsym list) * rsym list
type result = Ok of conf | Failed of int * conf

let rec z_of_pos (n : positive) : Z.t =
    match n with
    | XH -> Z.one
    | XO n -> Z.shift_left (z_of_pos n) 1
    | XI n -> Z.succ (Z.shift_left (z_of_pos n) 1)

let show_lsym (s : lsym): string =
    match s with
    | L_xs n -> "x^" ^ Z.to_string (z_of_pos n)
    | L_D    -> "D"
    | L_P    -> "P"
    | L_C0   -> "C0"
    | L_C1   -> "C1"
    | L_C2   -> "C2"
    | L_C3   -> "C3"
    | L_F0   -> "F0"
    | L_F1   -> "F1"
    | L_F2   -> "F2"
    | L_F3   -> "F3"
    | L_G0   -> "G0"
    | L_G1   -> "G1"
    | L_G2   -> "G2"
    | L_Fs n -> "F^" ^ Z.to_string (z_of_pos n)
    | L_Gs n -> "G^" ^ Z.to_string (z_of_pos n)
    | L_Hs n -> "H^" ^ Z.to_string (z_of_pos n)

let show_rsym (s : rsym): string =
    match s with
    | R_xs n -> "x^" ^ Z.to_string (z_of_pos n)
    | R_D    -> "D"
    | R_C    -> "C"
    | R_P    -> "P"
    | R_Gs n -> "G^" ^ Z.to_string (z_of_pos n)

let rec take n xs =
    if n == 0 then
        []
    else
        match xs with
        | [] -> []
        | x :: xs -> x :: take (n - 1) xs

let show_config (c : conf) =
    let ((d, l), r) = c in
    let l = List.rev_map show_lsym (take 500 l) in
    let r = List.rev (List.rev_map show_rsym r) in
    let d = match d with
            | Left -> "<"
            | Right -> ">"
            in
    let s = String.concat " " (l @ d :: r) in
    print_string s;
    print_newline ()

let show_result res =
    match res with
    | Ok c ->
        show_config c;
        print_string "ok\n"
    | Failed (k, c) ->
        show_config c;
        Printf.printf "%d steps to go\n" k
*)

let rec doit n c =
    if is_cycling c then
        Printf.printf "cycle found after %d steps\n" n
    else begin
        if n mod 1_000_000 == 0 then
            Printf.printf "%d steps done\n%!" n;
        match fullstep c with
        | Some c' -> doit (n + 1) c'
        | None ->
            Printf.printf "unknown transition after %d steps\n" n
    end

let _ = doit 0 initial
