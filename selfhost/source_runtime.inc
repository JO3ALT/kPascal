procedure InitSourceStream;
begin
  Read(stream_remaining);
  stream_current_char := #0;
  stream_has_char := false;
  stream_eof := stream_remaining <= 0
end;

procedure ReadSourceFromStdin;
begin
  InitSourceStream()
end;

procedure AdvanceSourceStream;
begin
  if stream_remaining > 0 then
    begin
      Read(source_next_code);
      stream_current_char := Chr(source_next_code);
      stream_remaining := stream_remaining - 1;
      stream_has_char := true;
      stream_eof := false
    end
  else
    begin
      stream_current_char := #0;
      stream_has_char := true;
      stream_eof := true
    end
end;

procedure PrimeSourceStream;
begin
  if not stream_has_char then
    AdvanceSourceStream()
end;
