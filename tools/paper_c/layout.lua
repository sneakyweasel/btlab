-- Keep the editorial Markdown readable; presentation belongs in this filter.
function Header(el)
  el.level = math.max(1, el.level - 1)
  return el
end

function Code(el)
  -- Identifiers, hashes and repository paths may wrap in narrow table cells.
  if not el.text:find('[{}\\#%%%s]') then
    return pandoc.RawInline('latex', '\\texttt{\\nolinkurl{' .. el.text .. '}}')
  end
end

function Table(el)
  return {pandoc.RawBlock('latex', '\\begingroup\\small'), el,
          pandoc.RawBlock('latex', '\\endgroup')}
end

function Pandoc(doc)
  local blocks = pandoc.List()
  local in_abstract = false
  local in_references = false
  for _, block in ipairs(doc.blocks) do
    if block.t == 'Header' and pandoc.utils.stringify(block.content) == 'References' then
      blocks:insert(block)
      blocks:insert(pandoc.RawBlock('latex', '\\begingroup\\small'))
      in_references = true
    elseif block.t == 'Header' and pandoc.utils.stringify(block.content) == 'Abstract' then
      in_abstract = true
      blocks:insert(pandoc.RawBlock('latex', '\\begin{abstract}'))
    elseif in_abstract and (block.t == 'Header' or
        pandoc.utils.stringify(block):match('^2020 Mathematics')) then
      blocks:insert(pandoc.RawBlock('latex', '\\end{abstract}'))
      in_abstract = false
      blocks:insert(block)
    else
      blocks:insert(block)
    end
  end
  if in_abstract then blocks:insert(pandoc.RawBlock('latex', '\\end{abstract}')) end
  if in_references then blocks:insert(pandoc.RawBlock('latex', '\\endgroup')) end
  return pandoc.Pandoc(blocks, doc.meta)
end

function Link(el)
  if el.target:match('^%.%./problems/') then
    el.target = 'https://github.com/sneakyweasel/btlab/blob/main/docs/problems/' .. el.target:sub(13)
  elseif el.target:match('%.md$') and not el.target:match('^https?://') then
    el.target = 'https://github.com/sneakyweasel/btlab/blob/main/docs/theory/' .. el.target
  end
  return el
end
