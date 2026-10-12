"""Fixed n=26 comparison against already existing exact data, not a new census."""
from pathlib import Path
import argparse,json
from counting_first_returns import run_check

if __name__=="__main__":
    ap=argparse.ArgumentParser()
    ap.add_argument("--reference-counts",type=Path,required=True)
    ap.add_argument("--output",type=Path,required=True)
    args=ap.parse_args()
    result=run_check(26,args.reference_counts)
    result["admission"]="fixed existing-data comparison through 26; no new coefficients beyond existing census"
    encoded=json.dumps(result,indent=2)+"\n"
    args.output.write_text(encoded)
    print(encoded,end="")
