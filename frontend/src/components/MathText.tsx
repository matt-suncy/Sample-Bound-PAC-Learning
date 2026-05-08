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
  // Split on $$...$$ (display) and $...$ (inline), in that order
  const parts = text.split(/(\$\$[\s\S]+?\$\$|\$[^$\n]+?\$)/g)

  const rendered = parts.map((part, i) => {
    if (part.startsWith('$$') && part.endsWith('$$') && part.length > 4) {
      const latex = part.slice(2, -2)
      return (
        <span
          key={i}
          style={{ display: 'block', textAlign: 'center', margin: '0.4em 0' }}
          dangerouslySetInnerHTML={{ __html: renderMath(latex, true) }}
        />
      )
    }
    if (part.startsWith('$') && part.endsWith('$') && part.length > 2) {
      const latex = part.slice(1, -1)
      return (
        <span
          key={i}
          dangerouslySetInnerHTML={{ __html: renderMath(latex, false) }}
        />
      )
    }
    return <span key={i}>{part}</span>
  })

  return isBlock ? (
    <p className={className} style={style}>{rendered}</p>
  ) : (
    <span className={className} style={style}>{rendered}</span>
  )
}
