import RMQ.Core.WordRAM.Optimization.CompactStatic

open RMQ.SuccinctFinal.PackedWordRAM
open RMQ.SuccinctFinal.PackedWordRAM.Structured
open RMQ.SuccinctFinal.PackedWordRAM.Optimization

#check compactAt_writesOnly
#check compactAt_writesOnly_interval
#check compact_run_frame
#check compact_run_ancestor_frame
#check compactAt_fits
#check compactAt_encoding_length
#print compactMaxCount
#print compactEncodingWords
#print CompactStaticConsumers.frame_expectedType
#print CompactStaticConsumers.fields_expectedType
#print CompactStaticConsumers.encoding_expectedType
#print axioms compactAt_writesOnly
#print axioms compactAt_writesOnly_interval
#print axioms compact_run_frame
#print axioms compact_run_ancestor_frame
#print axioms compactAt_fits
#print axioms compactAt_encoding_length
#print axioms CompactStaticConsumers.frame_expectedType
#print axioms CompactStaticConsumers.fields_expectedType
#print axioms CompactStaticConsumers.encoding_expectedType
