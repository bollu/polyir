let check name found expected =
  if found=expected then
    Printf.printf "%s => ok\n" name
  else
    Printf.printf "%s => ko\n" name;;
    
check "test1" Example.Tests.test1 false;  
check "test2" Example.Tests.test2 true;
check "test3" Example.Tests.test3 true;
check "test4" Example.Tests.test4 true
