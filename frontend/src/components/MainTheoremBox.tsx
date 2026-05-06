import type { TheoremNodeData } from '../data/graphData'
import { theoremNodes } from '../data/graphData'
import MathText from './MathText'

interface MainTheoremBoxProps {
  onOpenCode: (node: TheoremNodeData) => void
}

export default function MainTheoremBox({ onOpenCode }: MainTheoremBoxProps) {
  const node = theoremNodes.find(n => n.id === 'pac_sample_complexity_bound')!

  return (
    <div
      onClick={() => onOpenCode(node)}
      className="mx-auto cursor-pointer"
      style={{
        maxWidth: 760,
        background: '#EEF3FF',
        border: '1px solid #111111',
        boxShadow: '3px 3px 0 rgba(0,0,0,0.08)',
        padding: '2rem 2.5rem',
        marginTop: '2.5rem',
        marginBottom: '3rem',
        transition: 'box-shadow 0.15s ease',
      }}
      onMouseEnter={e => {
        ;(e.currentTarget as HTMLDivElement).style.boxShadow =
          '5px 5px 0 rgba(0,0,0,0.12)'
      }}
      onMouseLeave={e => {
        ;(e.currentTarget as HTMLDivElement).style.boxShadow =
          '3px 3px 0 rgba(0,0,0,0.08)'
      }}
    >
      {/* Theorem name in H2 */}
      <h2
        className="text-center font-inter font-bold text-[#111111] mb-3"
        style={{ fontSize: '1.75rem', lineHeight: 1.2 }}
      >
        {node.label}
      </h2>

      {/* Natural language statement */}
      <MathText
        text={node.naturalLanguageStatement}
        block
        className="text-center font-inter text-[#444444]"
        style={{ fontSize: '0.9375rem', lineHeight: 1.7, margin: 0 }}
      />

      <p
        className="text-center font-inter text-[#888888] mt-4"
        style={{ fontSize: '0.8rem' }}
      >
        Click to view Lean code
      </p>
    </div>
  )
}
