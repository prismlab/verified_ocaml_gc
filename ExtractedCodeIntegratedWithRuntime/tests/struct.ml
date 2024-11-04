type t = { a : int; mutable b : string }

let () =
  let x = { a = 10; b = "Hello" } in
  print_int x.a;
  print_newline ();
  print_string x.b;
  print_newline ();
  x.b <- "Hi Dipesh";
  print_string x.b;
  print_newline ()
