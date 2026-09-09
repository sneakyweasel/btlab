function Header(el)
  el.level = math.max(1, el.level - 1)
  return el
end
function Table(el)
  return {pandoc.RawBlock('latex', '\\begingroup\\small'), el,
          pandoc.RawBlock('latex', '\\endgroup')}
end
function Pandoc(doc)
  local blocks = pandoc.List()
  for _, block in ipairs(doc.blocks) do
    if block.t == 'Header' and pandoc.utils.stringify(block.content) == 'Acknowledgments and AI assistance' then
      blocks:insert(pandoc.RawBlock('latex', '\\needspace{12\\baselineskip}'))
    end
    if block.t == 'Para' and block.content[1] and block.content[1].t == 'Strong' then
      local label = pandoc.utils.stringify(block.content[1])
      if label:match('^Theorem') or label:match('^Proposition') or label:match('^Lemma') or label:match('^Hypothesis') then
        blocks:insert(pandoc.RawBlock('latex', '\\needspace{5\\baselineskip}'))
      end
    end
    blocks:insert(block)
  end
  return pandoc.Pandoc(blocks, doc.meta)
end
