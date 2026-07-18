import os
import pandas as pd

def add_tid_column_to_csvs(directory: str, encoding= 'utf-8'):
    # Initialize a counter for unique IDs
    unique_id = 1
    
    # Iterate over all files in the directory
    for filename in os.listdir(directory):
        # Check if the file is a CSV file
        if filename.endswith('.csv'):
            file_path = os.path.join(directory, filename)
            
            # Read the CSV file into a DataFrame
            df = pd.read_csv(file_path,encoding=encoding)
            
            # Add the tid column as the first column with unique IDs
            df.insert(0, 'tid', range(unique_id, unique_id + len(df)))
            
            # Update the unique_id for the next file
            unique_id += len(df)
            
            # Define the new filename with an underscore
            new_filename = filename.replace('.csv', '_.csv')
            new_file_path = os.path.join(directory, new_filename)
            
            # Save the modified DataFrame to the new CSV file
            df.to_csv(new_file_path, index=False, sep=",", encoding=encoding)
            
import re
from collections import defaultdict

def find_direct_transitive_derivations(file_path):
    """
    Given a file containing ASP facts such as

        pos(eqo("x","y"),id1).
        pos(eqo("y","z"),id2).
        pos(eqo("x","z"),id3).

    return all triples of ids corresponding to direct
    transitive derivations.
    """

    pattern = re.compile(
        r'pos\s*\(\s*eqo\s*\(\s*"([^"]+)"\s*,\s*"([^"]+)"\s*\)\s*,\s*([^)]+)\s*\)'
    )

    edge_to_id = {}
    outgoing = defaultdict(list)

    with open(file_path, "r") as f:
        for line in f:
            m = pattern.search(line)
            if not m:
                continue

            src, dst, ex_id = m.groups()
            ex_id = ex_id.strip()

            edge_to_id[(src, dst)] = ex_id
            outgoing[src].append(dst)

    derivations = set()

    # Find (a,b), (b,c), (a,c)
    for a, b in edge_to_id:
        for c in outgoing.get(b, []):
            if (a, c) in edge_to_id:
                ids = frozenset([
                    edge_to_id[(a, b)],
                    edge_to_id[(b, c)],
                    edge_to_id[(a, c)]
                ])

                if len(ids) == 3:
                    derivations.add(ids)

    return [set(d) for d in derivations]
            
if __name__ == "__main__":
    dir = "./lp/cora/80/s1/exs.pl"
    [print(trans) for trans in find_direct_transitive_derivations(dir)]