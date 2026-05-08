import { useState } from 'react'
import SyntaxHighlighter from 'react-syntax-highlighter'
import { definitions } from '../data/definitions'
import type { DefinitionEntry } from '../data/definitions'
import CodePopup from './CodePopup'
import MathText from './MathText'

// Minimal Abyss style for inline (non-interactive) code blocks
const inlineAbyssStyle: Record<string, React.CSSProperties> = {
  'code[class*="language-"]': {
    color: '#6688cc',
    background: '#000C18',
    fontFamily: '"Fira Code", "Consolas", monospace',
    fontSize: '12px',
    lineHeight: '1.6',
  } as React.CSSProperties,
  'pre[class*="language-"]': {
    background: '#000C18',
    margin: '0.6rem 0 0',
    padding: '0.9rem 1rem',
    overflow: 'auto',
    borderRadius: 0,
    border: '1px solid #1a2540',
  } as React.CSSProperties,
  comment: { color: '#384887', fontStyle: 'italic' },
  keyword: { color: '#4488cc' },
  string: { color: '#22aa44' },
  number: { color: '#f280d0' },
  'class-name': { color: '#ddbb88' },
  function: { color: '#ddbb88' },
  operator: { color: '#6688cc' },
  punctuation: { color: '#6688cc' },
}

export default function DefinitionsBox() {
  const [selected, setSelected] = useState<DefinitionEntry | null>(null)

  return (
    <>
      <div
        className="mx-auto"
        style={{
          maxWidth: 760,
          background: '#FFFFFF',
          border: '1px solid #111111',
          boxShadow: '3px 3px 0 rgba(0,0,0,0.08)',
          padding: '2rem 2.5rem',
          marginBottom: '4rem',
        }}
      >
        <h2
          className="text-center font-inter font-bold text-[#111111] mb-6"
          style={{ fontSize: '1.75rem', lineHeight: 1.2 }}
        >
          Definitions
        </h2>

        <ul style={{ listStyle: 'none', padding: 0, margin: 0 }}>
          {definitions.map((def, i) => (
            <li
              key={def.id}
              style={{
                paddingBottom: i < definitions.length - 1 ? '1.75rem' : 0,
                marginBottom: i < definitions.length - 1 ? '1.75rem' : 0,
                borderBottom:
                  i < definitions.length - 1 ? '1px solid #F0F0F0' : 'none',
              }}
            >
              {/* File tag */}
              <span
                style={{
                  fontFamily: 'monospace',
                  fontSize: '0.7rem',
                  color: '#888888',
                  display: 'block',
                  marginBottom: '2px',
                }}
              >
                {def.file}
                {def.isPrivate && ' · private'}
              </span>

              {/* Name */}
              <p style={{ margin: 0 }}>
                <strong
                  className="font-inter text-[#111111]"
                  style={{ fontSize: '0.9375rem' }}
                >
                  {def.name}
                </strong>
              </p>

              {/* Description */}
              <MathText
                text={def.description}
                block
                className="font-inter text-[#444444]"
                style={{ fontSize: '0.9375rem', lineHeight: 1.7, margin: '4px 0 0' }}
              />

              {/* Lean code block — click to open full popup */}
              <div
                onClick={() => setSelected(def)}
                style={{ cursor: 'pointer' }}
                title="Click to open full code panel"
              >
                <SyntaxHighlighter
                  language="haskell"
                  style={inlineAbyssStyle}
                  wrapLines={false}
                  PreTag="div"
                  customStyle={{ margin: '0.6rem 0 0' }}
                >
                  {def.leanCode}
                </SyntaxHighlighter>
              </div>
            </li>
          ))}
        </ul>
      </div>

      {selected && (
        <CodePopup node={selected} onClose={() => setSelected(null)} />
      )}
    </>
  )
}
