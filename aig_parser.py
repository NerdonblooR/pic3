import aiger


prefix = '/Users/haotan/Desktop/Desktop15/Projects/pic3/hwmcc/'
# Parser for ascii AIGER format.
aig1 = aiger.load(prefix + 'texasifetch1p8.aig')

print(aig1)