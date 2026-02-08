#!/usr/bin/env python3
"""Find uncovered branches from coverage.xml for a specific file."""

import sys
import xml.etree.ElementTree as ET

def find_uncovered_branches(xml_path, target_file):
    tree = ET.parse(xml_path)
    root = tree.getroot()
    
    results = []
    
    for package in root.findall('.//package'):
        for cls in package.findall('.//class'):
            filename = cls.get('filename', '')
            if target_file not in filename:
                continue
                
            print(f"File: {filename}")
            print(f"Line rate: {float(cls.get('line-rate', '0'))*100:.1f}%")
            print(f"Branch rate: {float(cls.get('branch-rate', '0'))*100:.1f}%")
            print()
            print("Uncovered/partial branches:")
            print("-" * 60)
            
            for line in cls.findall('.//line'):
                if line.get('branch') != 'true':
                    continue
                    
                cond_cov = line.get('condition-coverage', '')
                if '100%' in cond_cov:
                    continue
                    
                line_num = line.get('number', '0')
                hits = line.get('hits', '0')
                print(f"  Line {line_num}: {cond_cov} (hits: {hits})")
                results.append((int(line_num), cond_cov))
    
    if not results:
        print("  (none found - all branches covered or file not found)")
    
    return results

if __name__ == '__main__':
    if len(sys.argv) < 2:
        print("Usage: find-uncovered-branches.py <filename>")
        print("Example: find-uncovered-branches.py memory.c")
        sys.exit(1)
    
    target = sys.argv[1]
    find_uncovered_branches('coverage-report/coverage.xml', target)
