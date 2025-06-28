
-- you asked about "for loops" in Lean!

def myprint : String → IO Unit 
  | "ack" => IO.println "wow"
  | s => IO.println (s ++ " etc")


def xs : List String := [ "foo", "bar", "ack", "baz", "bif" ]

#check forM
#check forM xs myprint
#eval forM xs myprint

def chstr : String -> String
 | s => s ++ " abc"

#check List.map
#eval xs

#check List.map chstr xs
#eval List.map chstr xs

