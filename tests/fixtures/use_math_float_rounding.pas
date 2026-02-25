program usemathfloatrounding;
(* $I math.pas *)
begin
  WriteLn(f_trunc(-2.9));
  WriteLn(f_round(-2.6));
  WriteLn(f_round(2.5));
  WriteLn(floor(-2.1));
  WriteLn(floor(2.1));
  WriteLn(ceil(-2.1));
  WriteLn(ceil(2.1))
end.
