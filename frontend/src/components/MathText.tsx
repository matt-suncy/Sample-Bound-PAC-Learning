import React from 'react'
import katex from 'katex'
import 'katex/dist/katex.min.css'

// Renders a string that may contain $...$ (inline) or $$...$$ (display) math.
// Example: "The error is $\\varepsilon$" renders with KaTeX inline math.

interface MathTextProps {
  text: string
  className?: string
  style?: React.CSSProperties
  block?: boolean   // if true, wraps in <p> instead of <span>
}

function renderMath(latex: string, display: boolean): string {
  return katex.renderToString(latex, {
    throwOnError: false,
    displayMode: display,
    trust: false,
  })
}

export default function MathText({ text, className, style, block: isBlock }: MathTextProps) {
  // 1. Split on $$...$$ (display math) first to preserve multiline math blocks
  const parts = text.split(/(\$\$[\s\S]+?\$\$)/g)

  const renderedBlocks = parts.map((part, partIdx) => {
    // If it's a display math block
    if (part.startsWith('$$') && part.endsWith('$$') && part.length > 4) {
      const latex = part.slice(2, -2)
      return (
        <span
          key={partIdx}
          style={{ display: 'block', textAlign: 'center', margin: '0.4em 0' }}
          dangerouslySetInnerHTML={{ __html: renderMath(latex, true) }}
        />
      )
    }

    // It's a text block. Split into lines to apply list styling.
    const lines = part.split('\n')
    return (
      <React.Fragment key={partIdx}>
        {lines.map((line, lineIdx) => {
          // Check if line is a list item (e.g. "    1. ", "        a. ")
          const listMatch = line.match(/^(\s+)([0-9]+|[a-z])\.\s(.*)/)
          
          let isList = false
          let spaces = ''
          let marker = ''
          let contentStr = line

          if (listMatch) {
            isList = true
            spaces = listMatch[1]
            marker = listMatch[2] + '. '
            contentStr = listMatch[3]
          }

          // Parse inline math $...$ inside the line content
          const inlineParts = contentStr.split(/(\$[^$\n]+?\$)/g)
          const renderedInline = inlineParts.map((inlinePart, inlineIdx) => {
            if (inlinePart.startsWith('$') && inlinePart.endsWith('$') && inlinePart.length > 2) {
              const latex = inlinePart.slice(1, -1)
              return (
                <span
                  key={inlineIdx}
                  dangerouslySetInnerHTML={{ __html: renderMath(latex, false) }}
                />
              )
            }
            return <span key={inlineIdx}>{inlinePart}</span>
          })

          if (isList) {
            return (
              <div key={lineIdx} style={{ display: 'flex', marginTop: '0.25rem' }}>
                <span style={{ whiteSpace: 'pre' }}>{spaces}</span>
                <span style={{ flexShrink: 0 }}>{marker}</span>
                <span style={{ flexGrow: 1 }}>{renderedInline}</span>
              </div>
            )
          }

          // Normal line
          return (
            <React.Fragment key={lineIdx}>
              {renderedInline}
              {lineIdx < lines.length - 1 && '\n'}
            </React.Fragment>
          )
        })}
      </React.Fragment>
    )
  })

  // Root element must be a div if it contains divs
  return isBlock ? (
    <div className={className} style={style}>{renderedBlocks}</div>
  ) : (
    <span className={className} style={style}>{renderedBlocks}</span>
  )
}
