import React from 'react';

export const LeanCode = ({ code }: { code: string }) => {
  const lines = code.split('\n');
  let inBlockComment = false;
  
  return (
    <pre className="font-mono text-sm md:text-base p-6 md:p-8 overflow-x-auto leading-relaxed text-[#D4D4D4]">
      <code>
        {lines.map((line, i) => {
          if (line.trim().startsWith('/--') || line.trim().startsWith('/*')) {
            inBlockComment = true;
          }
          
          const isComment = inBlockComment || line.trim().startsWith('--');
          
          if (line.trim().endsWith('-/') || line.trim().endsWith('*/')) {
            inBlockComment = false;
            return <div key={i} className="text-[#6A9955] italic">{line || ' '}</div>;
          }

          if (isComment) {
            return <div key={i} className="text-[#6A9955] italic">{line || ' '}</div>;
          }
          if (!line) return <div key={i}>&nbsp;</div>;

          const parts = line.split(/(\s+|⟶|≫|≅|⊥_|⊤_|𝟙|:=|=|{|}|\[|\]|\(|\))/);
          return (
            <div key={i}>
              {parts.map((part, j) => {
                if (['import', 'open', 'variable', 'def', 'example', 'by', 'simp', 'theorem', 'lemma', 'exact', 'rfl', 'universe', 'where', 'section', 'end'].includes(part)) {
                  return <span key={j} className="text-[#C586C0] font-semibold">{part}</span>;
                }
                if (['⟶', '≫', '𝟙', ':=', '=', '≅', '⊥_', '⊤_'].includes(part)) {
                  return <span key={j} className="text-[#569CD6]">{part}</span>;
                }
                if (['Type', 'Category', 'Prop', 'Subsingleton'].includes(part)) {
                  return <span key={j} className="text-[#4EC9B0]">{part}</span>;
                }
                return <span key={j}>{part}</span>;
              })}
            </div>
          );
        })}
      </code>
    </pre>
  );
};
