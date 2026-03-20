procedure ReadSourceFromStdin;
var i: integer;
begin
  i := 0;
  while not SeekEof do
    begin
      Read(SourceText[i]);
      i := i + 1;
      if i >= MAX_SOURCE_LEN then
        break
    end;
  source_len := i;
end;
